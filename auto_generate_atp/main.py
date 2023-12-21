import argparse
import torch.multiprocessing as mp

from train_ddp import main as gpt2_pretrain
from train_ddp_batched import main as gpt2_batched_pretrain
from train_retro import main as gpt2_train_retro
from transformers import GPT2Tokenizer, GPT2Model
from retrieval import Retrieval
from utils import split_file


from utils import init_distributed

parser = argparse.ArgumentParser()
parser.add_argument(
    '--devices', type=str, nargs='+', default=['0', '1', '2', '3'],
    help='which devices to use on local machine')
parser.add_argument(
    '--port', type=int,
    default=4925
)
parser.add_argument(
    '--data_feet_type', type=str, default='batched',
    help="choose from `batched` and `slide_window`. batch for proofstep fine-tune and slide window for large crop pre-train." 
)
parser.add_argument('--n_ctx', default=768, type=int, help="length of the sequence")
parser.add_argument('--raw_data_path', default='data/train_proofstep.txt',
                    type=str, required=False, help='原始训练语料')
parser.add_argument('--test_data_path', default='data/test.txt',
                    type=str, required=False, help='测试数据')
parser.add_argument('--valid_data_path', default='data/valid.txt',
                    type=str, required=False, help='测试数据')                    
parser.add_argument('--tokenized_data_path', default='data/tokenized/', type=str, required=False,
                    help='tokenized语料存放位置')
parser.add_argument('--split_data_path', default='data/split/', type=str, required=False,
                    help='切分后的语料存放位置')
parser.add_argument('--raw', action='store_true', help='是否先做tokenize')
parser.add_argument('--epochs', default=5, type=int,
                    required=False, help='训练循环')
parser.add_argument('--batch_size', default=2, type=int,
                    required=False, help='训练batch size')
parser.add_argument('--lr', default=2.5e-4, type=float,
                    required=False, help='学习率')
parser.add_argument('--warmup_steps', default=2000,
                    type=int, required=False, help='warm up步数')
parser.add_argument('--log_step', default=1, type=int, required=False,
                    help='多少步汇报一次loss, 设置为gradient accumulation的整数倍')
parser.add_argument('--stride', default=178, type=int,
                    required=False, help='训练时取训练数据的窗口步长')
parser.add_argument('--gradient_accumulation', default=64,
                    type=int, required=False, help='梯度积累')
parser.add_argument('--fp16', action='store_true', help='混合精度')
parser.add_argument('--max_grad_norm', default=1.0, type=float, required=False)
parser.add_argument('--num_pieces', default=100, type=int,
                    required=False, help='将训练语料分成多少份')
parser.add_argument('--min_length', default=2, type=int,
                    required=False, help='最短收录文章长度')
parser.add_argument('--output_dir', default='model/',
                    type=str, required=False, help='模型输出路径')
parser.add_argument('--pretrained_model', default='gpt2-medium',
                    type=str, required=False, help='模型训练起点路径')
parser.add_argument('--model_type', default='gpt2-medium',
                    type=str, required=False, help='模型起点路径')
parser.add_argument('--writer_dir', default='tensorboard_summary/',
                    type=str, required=False, help='Tensorboard路径')



# add retrival argument
parser.add_argument('--retrieval', action='store_true', help='是否进行retrieval')
parser.add_argument('--reprocess_retrieval',  action='store_true',
                    help="重新进行retrieval索引建立")
parser.add_argument('--knn', default=5, type=int, help="选取几个最近邻作为Memory")
parser.add_argument('--chunks_memmap_path', default='data/retrieval/train.chunks.dat', 
                    help="input_id存储的路径")
parser.add_argument('--seq_dict_memmap_path', default='data/retrieval/train.seq_dict.dat',
                    help="文件序号和文件中行号到chunk_id的对应")
parser.add_argument('--processed_stats_json_path', default='data/retrieval/processed-stats.json',
                    help="存储retrival处理完成后一些状态的json路径")
parser.add_argument('--faiss_index_filename', default='data/retrieval/knn.index',
                    help='存储faiss建立好的index')
parser.add_argument('--chunk_size', default=400, type=int,
                    help="单个retrieval出来的条目的长度, 与knn个数共同组成memory大小")
parser.add_argument('--max_chunks', default=1_000_000, type=int,
                    help="作为memory的chunks的个数的最大值, 训练集中不能超过这个个数")
parser.add_argument('--retrieval_batch_size', default=64, type=int,
                    help="retrieval中文本encoder使用的batch_size")
parser.add_argument('--retrieval_model_path', default='model0421/model_epoch2',
                    help="retrieval中文本encoder使用的预训练向量的路径")

parser.add_argument('--retrieval_benchmark', action='store_false', 
                    help='是否计算retrival的benchmark')
parser.add_argument('--resume_checkpoint', action='store_true',
                    help='resume checkpoint from last training')



def preprocess_retrieval(args, devices):
    # use only one gpu
    import os
    device = 'cuda:' + devices[0].split(':')[-1]
    
    if not os.path.exists(args.split_data_path):
        split_file(data_path=args.raw_data_path, split_data_path=args.split_data_path, num_pieces=args.num_pieces)
        
    tokenizer = GPT2Tokenizer.from_pretrained(args.pretrained_model)
    tokenizer.add_special_tokens({'pad_token': '<|pad|>'})
    model = GPT2Model.from_pretrained(args.retrieval_model_path).to(device)
    model.resize_token_embeddings(len(tokenizer))
    retrieval = Retrieval(
        tokenizer=tokenizer,
        model=model,
        args=args
    )

    if args.retrieval_benchmark:
        retrieval.benchmark_retrival()

    del tokenizer
    del model 
    return retrieval

def process_main(rank, args, world_size, devices, port):
    import os
    os.environ['CUDA_VISIBLE_DEVICES'] = str(devices[rank].split(':')[-1])
    os.environ['NCCL_DEBUG'] = 'INFO'
    # print(os.environ['CUDA_VISIBLE_DEVICES'])

    import logging
    logging.basicConfig()
    logger = logging.getLogger()
    
    world_size, rank = init_distributed(port, rank_and_world_size=(rank, world_size))

    # -- make sure all processes correctly initialized torch-distributed
    logger.info(f'Running GPT2 {args.data_feet_type} pretrain (rank: {rank}/{world_size})')

    # -- turn off info-logging for ranks > 0, otherwise too much std output
    if rank == 0:
        logger.setLevel(logging.INFO)
    else:
        logger.setLevel(logging.ERROR)
    
    if args.retrieval:
        return gpt2_train_retro(args)
    
    if args.data_feet_type == 'batched':
        return gpt2_batched_pretrain(args)
    elif args.data_feet_type == 'slide_window':
        return gpt2_pretrain(args)

def main(args):
    if args.retrieval:
        preprocess_retrieval(args, args.devices)
    print('args:\n' + args.__repr__())
    num_gpus = len(args.devices)
    print(f'num_gpus: {num_gpus}')
    mp.spawn(
        process_main,
        nprocs=num_gpus,
        args=(args, num_gpus, args.devices, args.port))

if __name__ == '__main__':
    args = parser.parse_args()
    print('args:\n' + args.__repr__())
    num_gpus = len(args.devices)
    print(f'num_gpus: {num_gpus}')

    main(args)