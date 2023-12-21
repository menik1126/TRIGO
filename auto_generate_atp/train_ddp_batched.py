import json
from transformers import GPT2Tokenizer, GPT2LMHeadModel, GPT2Config, AdamW
from retro_model import MemoryLMHeadModel
from transformers import get_linear_schedule_with_warmup
import torch
import os
import random
import numpy as np
import sys
import logging
from copy import copy
from torch.utils.tensorboard import SummaryWriter
from datetime import datetime
from tqdm import tqdm
from torch.nn import DataParallel

from utils import split_file, init_distributed
from data_manager import get_dataloader_batced, get_test_dataloader
# from tokenizations.bpe_tokenizer import get_encoder

from torch.nn.parallel import DistributedDataParallel





# --
log_timings = True
log_freq = 300


_GLOBAL_SEED = 0
np.random.seed(_GLOBAL_SEED)
torch.manual_seed(_GLOBAL_SEED)
torch.backends.cudnn.benchmark = True

logging.basicConfig(stream=sys.stdout, level=logging.INFO)
logger = logging.getLogger()


def main(args):
    full_tokenizer = GPT2Tokenizer.from_pretrained(args.model_type)
    full_tokenizer.add_special_tokens({'pad_token': '<|pad|>'})
    device = 'cuda:0' if torch.cuda.is_available() else 'cpu'
    print('using device:', device)

    # -- pretrain parameter
    raw_data_path = args.raw_data_path
    test_data_path = args.test_data_path
    valid_data_path = args.valid_data_path
    split_data_path = args.split_data_path
    raw = args.raw  # 选择是否从零开始构建数据集
    epochs = args.epochs
    batch_size = args.batch_size
    lr = args.lr
    warmup_steps = args.warmup_steps
    log_step = args.log_step
    gradient_accumulation = args.gradient_accumulation
    fp16 = args.fp16  # 不支持半精度的显卡请勿打开
    max_grad_norm = args.max_grad_norm
    num_pieces = args.num_pieces
    output_dir = args.output_dir
    tb_writer = SummaryWriter(log_dir=args.writer_dir)
    assert log_step % gradient_accumulation == 0

    if not os.path.exists(output_dir):
        os.mkdir(output_dir)

    if raw:
        print('building files')
        split_file(data_path=[raw_data_path], split_data_path=split_data_path, num_pieces=num_pieces)
        print('files built')

    # -- init torch distributed backend
    world_size, rank = init_distributed()
    logger.info(f'Initialized (rank/world-size) {rank}/{world_size}')

    if args.resume_checkpoint and os.path.exists(output_dir + 'model_last/model'):
        model_path = output_dir + 'model_last/model'
    else:
        model_path = args.pretrained_model
    model = MemoryLMHeadModel.from_pretrained(model_path)
    # model = MemoryLMHeadModel.from_pretrained(local_model_path)
    model.resize_token_embeddings(len(full_tokenizer))
    optimizer = AdamW(model.parameters(), lr=lr, correct_bias=True)
    loaded_stats = None
    # This will load the model, but infomation from dataloader will be loss
    # TODO: fix: FP16 will ocurr "AssertionError"
    if args.resume_checkpoint and  os.path.exists(output_dir + 'model_last'):
        loaded_stats = load_model_state(output_dir, 'model_last')
    model.train()
    model.to(device)
    if world_size > 1:
        try:
            """
            Recursively traverse module and its children to replace all instances of
            ``torch.nn.modules.batchnorm._BatchNorm`` with :class:`apex.parallel.SyncBatchNorm`.
            """
            # import apex
            # process_group = apex.parallel.create_syncbn_process_group(0)
            # model = apex.parallel.convert_syncbn_model(model, process_group=process_group)
            model = torch.nn.SyncBatchNorm.convert_sync_batchnorm(model)
        except:
            # logger.info("Please install apex from https://www.github.com/nvidia/apex")
            logger.info("Batch normalization is not syncronized now")
        
    scaler = torch.cuda.amp.GradScaler(enabled=fp16)
    if world_size > 1:
        model = DistributedDataParallel(model, broadcast_buffers=False, find_unused_parameters=False)

    full_len = 0
    logger.info('calculating total steps')
    for i in tqdm(range(num_pieces)):
        with open(split_data_path + 'split_train_{}.txt'.format(i), 'r') as f:
            full_len += len(f.readlines())
    total_steps = int(full_len * epochs / batch_size / gradient_accumulation)
    logger.info('total steps = {}'.format(total_steps))

    
    scheduler = get_linear_schedule_with_warmup(optimizer, num_warmup_steps=warmup_steps,
                                                          num_training_steps=total_steps)

    logger.info('starting training')
    overall_step = loaded_stats['step'] if loaded_stats is not None else 0
    running_loss = 0
    best_ppl = 1_000_000 if loaded_stats is None else loaded_stats['ppl']
    start_epoch = 0 if loaded_stats is None else loaded_stats['epoch']
    for epoch in range(start_epoch, epochs):
        logger.info('epoch {}'.format(epoch + 1))
        now = datetime.now()
        logger.info('time: {}'.format(now))
        x = np.linspace(0, num_pieces - 1, num_pieces, dtype=np.int32)
        random.shuffle(x)
        piece_num = 0
        for i in x:
            dataloader = get_dataloader_batced(args, full_tokenizer, i, world_size, rank)
            for batch in dataloader:
                with torch.cuda.amp.autocast(enabled=fp16):
                    input_ids, attention_mask, labels = batch[0].to(device), batch[1].to(device), batch[2].to(device)

                    # forward pass
                    # TODO: verify the correctness of the loss calculated
                    outputs = model.forward(input_ids=input_ids, attention_mask=attention_mask, labels=labels, memory=None)
                    loss, _ = outputs[:2]

                    if gradient_accumulation > 1:
                        loss = loss / gradient_accumulation

                scaler.scale(loss).backward()
                torch.nn.utils.clip_grad_norm_(model.parameters(), max_grad_norm)
    
                #  optimizer step
                if (overall_step + 1) % gradient_accumulation == 0:
                    running_loss += loss.item()
                    scaler.step(optimizer)
                    scaler.update()
                    optimizer.zero_grad()
                    scheduler.step()
                if (overall_step) % log_step == 0:
                    tb_writer.add_scalar('loss', loss.item() * gradient_accumulation, overall_step)
                    logger.info('now time: {}:{}. Step {} of piece {} of epoch {}, loss {}'.format(
                        datetime.now().hour,
                        datetime.now().minute,
                        overall_step + 1,
                        piece_num,
                        epoch + 1,
                        running_loss * gradient_accumulation / (log_step / gradient_accumulation)))
                    running_loss = 0
                overall_step += 1

                if (overall_step / gradient_accumulation) % 1000 == 0:
                    ppl = test_ppl(args, valid_data_path, full_tokenizer, model, device, world_size, rank, overall_step)
                    stats = {
                            'time': f'Day: {datetime.now().month}/{datetime.now().day}, Time:{datetime.now().hour}:{datetime.now().minute}',
                            'step': overall_step,
                            'piece_num': piece_num,
                            'epoch': epoch,
                            'running_loss': running_loss * gradient_accumulation / (log_step / gradient_accumulation),
                            'ppl': ppl
                        }
                    if ppl < best_ppl:
                        best_ppl = ppl
                        if rank == 0:
                            save_model(model, optimizer, output_dir, 'best_model', stats)
                    save_model(model, optimizer, output_dir, 'model_last', stats)
            piece_num += 1

        # save model only in the first process.
        if rank == 0:
            stats = {
                        'time': f'Day: {datetime.now().month}/{datetime.now().day}, Time:{datetime.now().hour}:{datetime.now().minute}',
                        'step': overall_step,
                        'piece_num': piece_num,
                        'epoch': epoch,
                        'running_loss': running_loss * gradient_accumulation / (log_step / gradient_accumulation),
                        'ppl': ppl
                    }
            save_model(model, optimizer, output_dir, f'model_epoch{epoch + 1}', stats)
        logger.info('epoch {} finished'.format(epoch + 1))

        then = datetime.now()
        logger.info('time: {}'.format(then))
        logger.info('time for one epoch: {}'.format(then - now))

    if rank ==0:
        logger.info('training finished')
        save_model(model, optimizer, output_dir, 'final_model', stats)

def save_model(model, optimizer, output_dir, model_path, stats):
    logger.info(f'saving model for {model_path}')
    if not os.path.exists(output_dir + model_path):
        os.mkdir(output_dir + model_path)
    if not os.path.exists(output_dir + model_path + '/model'):
        os.mkdir(output_dir + model_path + '/model')
    model_to_save = model.module if hasattr(model, 'module') else model
    model_to_save.save_pretrained(output_dir + model_path + '/model')
    torch.save({
            'optimizer_state_dict': optimizer.state_dict(),
            }, output_dir + model_path + '/state_dict.pt')
    with open(output_dir + model_path + '/stats.json', 'w') as f:
        json.dump(stats, f)

def load_model_state(output_dir, model_path):
    # load model is not used
    # stats from dataloader will be lost
    if not os.path.exists(output_dir + model_path):
        stats = {'step': 0,
                'piece_num': 0,
                'epoch': 0,
                'ppl':1_000_000}
        return stats
    with open(output_dir + model_path + '/stats.json') as f:
        stats = json.loads(f.read())
    print(f'Loaded model stat from {output_dir + model_path} sucessfully...')
    return stats


def test_ppl(args, data_path, tokenizer, model, device, world, rank, step):
    dataloader = get_test_dataloader(args, data_path, tokenizer, world, rank)
    nll = []
    for batch in dataloader:
        input_ids, attention_mask, labels = batch
        input_ids, attention_mask, labels = input_ids.squeeze().to(device), \
                            attention_mask.squeeze().to(device), labels.squeeze().to(device)
        

        with torch.no_grad():
            outputs = model(input_ids, attention_mask=attention_mask,labels=labels)
            neg_log_likelihood = outputs[0]

        nll.append(neg_log_likelihood.item())
    logger.info(f'Step {step}, Test ppl {sum(nll) / len(nll)}')
    return sum(nll) / len(nll)


