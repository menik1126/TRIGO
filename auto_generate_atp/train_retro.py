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
from data_manager import get_dataloader_retro
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
    full_tokenizer = GPT2Tokenizer.from_pretrained(args.pretrained_model)
    full_tokenizer.add_special_tokens({'pad_token': '<|pad|>'})

    device = 'cuda:0' if torch.cuda.is_available() else 'cpu'
    print('using device:', device)

    # -- pretrain parameter
    raw_data_path = args.raw_data_path
    split_data_path = args.split_data_path
    raw = args.raw  # 选择是否从零开始构建数据集
    epochs = args.epochs
    batch_size = args.batch_size
    lr = args.lr
    warmup_steps = args.warmup_steps
    log_step = args.log_step
    stride = args.stride
    gradient_accumulation = args.gradient_accumulation
    fp16 = args.fp16  # 不支持半精度的显卡请勿打开
    max_grad_norm = args.max_grad_norm
    num_pieces = args.num_pieces
    min_length = args.min_length
    output_dir = args.output_dir
    tb_writer = SummaryWriter(log_dir=args.writer_dir)
    assert log_step % gradient_accumulation == 0

    if not os.path.exists(output_dir):
        os.mkdir(output_dir)

    if raw:
        print('building files')
        split_file(data_path=raw_data_path, split_data_path=split_data_path, num_pieces=num_pieces)
        print('files built')

    # -- init torch distributed backend
    world_size, rank = init_distributed()
    logger.info(f'Initialized (rank/world-size) {rank}/{world_size}')

    model = MemoryLMHeadModel.from_pretrained(args.pretrained_model)
    model.resize_token_embeddings(len(full_tokenizer))
    model.train()
    model.to(device)
    if world_size > 1:
        try:
            """
            Recursively traverse module and its children to replace all instances of
            ``torch.nn.modules.batchnorm._BatchNorm`` with :class:`apex.parallel.SyncBatchNorm`.
            """
            import apex
            process_group = apex.parallel.create_syncbn_process_group(0)
            model = apex.parallel.convert_syncbn_model(model, process_group=process_group)
        except:
            logger.info("Please install apex from https://www.github.com/nvidia/apex")
            logger.info("Batch normalization is not syncronized now")
        
    scaler = torch.cuda.amp.GradScaler(enabled=fp16)
    if world_size > 1:
        model = DistributedDataParallel(model, broadcast_buffers=False, find_unused_parameters=False)

    # # -- calculate model parameter
    # num_parameters = 0
    # parameters = model.parameters()
    # for parameter in parameters:
    #     num_parameters += parameter.numel()
    # logger.info('number of parameters: {}'.format(num_parameters))

    full_len = 0
    logger.info('calculating total steps')
    for i in tqdm(range(num_pieces)):
        with open(split_data_path + 'split_train_{}.txt'.format(i), 'r') as f:
            full_len += len(f.readlines())
    total_steps = int(full_len * epochs / batch_size / gradient_accumulation)
    logger.info('total steps = {}'.format(total_steps))

    optimizer = AdamW(model.parameters(), lr=lr, correct_bias=True)
    scheduler = get_linear_schedule_with_warmup(optimizer, num_warmup_steps =warmup_steps,
                                                          num_training_steps =total_steps)

    logger.info('starting training')
    overall_step = 0
    running_loss = 0
    for epoch in range(epochs):
        logger.info('epoch {}'.format(epoch + 1))
        now = datetime.now()
        logger.info('time: {}'.format(now))
        x = np.linspace(0, num_pieces - 1, num_pieces, dtype=np.int32)
        random.shuffle(x)
        piece_num = 0
        for i in x:
            step = 0
            dataloader = get_dataloader_retro(args, full_tokenizer, i, world_size, rank)
            for batch in dataloader:
                with torch.cuda.amp.autocast(enabled=fp16):
                    input_ids, memory_hidden_states, memory_attention_mask = batch
                    input_ids, memory_hidden_states, memory_attention_mask = \
                        input_ids.to(device), memory_hidden_states.to(device), memory_attention_mask.float().to(device)
                    
                    labels = torch.where(input_ids!=full_tokenizer.pad_token_id, input_ids, -100)
                    # -- set padded token to -100 so that the CE loss will ignore these tokens
                    attention_mask = (input_ids != full_tokenizer.pad_token_id).float()

                    # forward pass
                    # TODO: verify the correctness of the loss calculated
                    outputs = model.forward(input_ids=input_ids, attention_mask=attention_mask, labels=labels, 
                                memory=memory_hidden_states, memory_attention_mask=memory_attention_mask, memory_fusion_layer=[18])
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
                if (overall_step + 1) % log_step == 0:
                    tb_writer.add_scalar('loss', loss.item() * gradient_accumulation, overall_step)
                    logger.info('now time: {}:{}. Step {} of piece {} of epoch {}, loss {}'.format(
                        datetime.now().hour,
                        datetime.now().minute,
                        step + 1,
                        piece_num,
                        epoch + 1,
                        running_loss * gradient_accumulation / (log_step / gradient_accumulation)))
                    running_loss = 0
                overall_step += 1
                step += 1
            piece_num += 1

        # save model only in the first process.
        if rank == 0:
            logger.info('saving model for epoch {}'.format(epoch + 1))
            if not os.path.exists(output_dir + 'model_epoch{}'.format(epoch + 1)):
                os.mkdir(output_dir + 'model_epoch{}'.format(epoch + 1))
            model_to_save = model.module if hasattr(model, 'module') else model
            model_to_save.save_pretrained(output_dir + 'model_epoch{}'.format(epoch + 1))
            # torch.save(scheduler.state_dict(), output_dir + 'model_epoch{}/scheduler.pt'.format(epoch + 1))
            # torch.save(optimizer.state_dict(), output_dir + 'model_epoch{}/optimizer.pt'.format(epoch + 1))
        logger.info('epoch {} finished'.format(epoch + 1))

        then = datetime.now()
        logger.info('time: {}'.format(then))
        logger.info('time for one epoch: {}'.format(then - now))

    if rank ==0:
        logger.info('training finished')
        if not os.path.exists(output_dir + 'final_model'):
            os.mkdir(output_dir + 'final_model')
        model_to_save = model.module if hasattr(model, 'module') else model
        model_to_save.save_pretrained(output_dir + 'final_model')
        # torch.save(scheduler.state_dict(), output_dir + 'final_model/scheduler.pt')
        # torch.save(optimizer.state_dict(), output_dir + 'final_model/optimizer.pt')


