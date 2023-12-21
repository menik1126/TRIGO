import argparse
import os
import pandas as pd
from tqdm import tqdm

from main import main as train_main
from eval_search import main as search_main
from utils import reset_folder_, split_file, copy_folder_



BUCKETS = list('ABCDEFGHIJK')
parser = argparse.ArgumentParser()
parser.add_argument(
    '--devices', type=str, nargs='+', default=['4', '5'],
    help='which devices to use on local machine')
parser.add_argument(
    '--port', type=int,
    default=4923
)
parser.add_argument(
    '--data_feet_type', type=str, default='batched',
    help="choose from `batched` and `slide_window`. batch for proofstep fine-tune and slide window for large crop pre-train." 
)
parser.add_argument('--n_ctx', default=750, type=int, help="length of the sequence")
parser.add_argument('--split_data_path', default='data/split/', type=str, required=False,
                    help='切分后的语料存放位置')
parser.add_argument('--test_data_path', default='data/test.txt',
                    type=str, required=False, help='测试数据')
parser.add_argument('--valid_data_path', default='data/valid.txt',
                    type=str, required=False, help='测试数据')                    
parser.add_argument('--epochs', default=5, type=int,
                    required=False, help='训练循环')
parser.add_argument('--batch_size', default=4, type=int,
                    required=False, help='训练batch size')
parser.add_argument('--lr', default=0.00025, type=float,
                    required=False, help='学习率')
parser.add_argument('--warmup_steps', default=2000,
                    type=int, required=False, help='warm up步数')
parser.add_argument('--log_step', default=1, type=int, required=False,
                    help='多少步汇报一次loss, 设置为gradient accumulation的整数倍')
parser.add_argument('--stride', default=178, type=int,
                    required=False, help='训练时取训练数据的窗口步长')
parser.add_argument('--gradient_accumulation', default=1,
                    type=int, required=False, help='梯度积累')
parser.add_argument('--fp16', action='store_true', help='混合精度')
parser.add_argument('--max_grad_norm', default=1.0, type=float, required=False)
parser.add_argument('--num_pieces', default=100, type=int,
                    required=False, help='将训练语料分成多少份')
parser.add_argument('--min_length', default=2, type=int,
                    required=False, help='最短收录文章长度')
parser.add_argument('--output_dir', default='model/',
                    type=str, required=False, help='模型输出路径')
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


parser.add_argument('--dec_names_path', default='data/test.names',
                    type=str, required=False, help='原始语料')
parser.add_argument('--search_states', default='data/search_state.txt',
                    type=str, required=False, help='保存搜索进度')
parser.add_argument('--model_type', default='../pretrained_model/en_model/gpt2-medium-local/',
                    type=str, required=False, help='模型起点路径')
parser.add_argument('--temperature', default=1, type=float,
                    required=False, help='generation temperature')
parser.add_argument('--max_length', default=200, type=int,
                    required=False, help='generation maximun length')
parser.add_argument('--topk', default=0, type=int,
                    required=False, help='generation top-k for top-k sampling')
parser.add_argument('--topp', default=0, type=int,
                    required=False, help='generation top-p for top-p sampling')
parser.add_argument('--repetition_penalty', default=0, type=int,
                    required=False, help='generation repetition penalty')
parser.add_argument('--e', default=8, type=int,
                    required=False, help='number of search tactic per goal')
parser.add_argument('--d', default=128, type=int,
                    required=False, help='deepest search depth')
parser.add_argument('--n_retry', default=0, type=int,
                    required=False, help='number of time regenerating the tactics when #e tactic is not applicable')
parser.add_argument('--try_intros', default=True, type=bool,
                    required=False, help='use `try {intros}` tactic for every proof after init search')
parser.add_argument('--use_value_function', default=True, type=bool,
                    required=False, help='use value function to evaluate goals')
parser.add_argument('--resume_checkpoint', action='store_true',
                    help='resume checkpoint from last training')


class ExpertIteration:
    def __init__(self, args) -> None:
        self.args = args
        self.proofsize_path = 'data/proofsize_tmp'
        self.proofstep_path = 'data/proofstep_tmp'

    def pretrain(self, args):
        # pretrain model to get `theta 0` model
        reset_folder_('data/split/')
        args.raw = False
        split_file(['data/train_proofstep.txt', 'data/mix1.txt'], split_data_path='data/split/', num_pieces=100)
        args.retrieval=False
        args.raw_data_path = None
        args.data_feet_type = 'batched'
        args.output_dir = 'model_theta0/'
        args.pretrained_model = 'gpt2-medium'
        args.epochs = 10
        train_main(args)
        
    def generate_new_proofsize_and_proofstep_data(self, args, model_path, use_value_function, k):
        if os.path.exists(args.search_states):
            with open(args.search_states, 'r') as f:
                lines = f.readlines()
                # number of lines in `train.names`, meaning all the search is finished
            if len(lines) == 30787:
                copy_folder_(self.proofsize_path, f'{self.proofsize_path}_{k}')
                copy_folder_(self.proofstep_path, f'{self.proofstep_path}_{k}')
                reset_folder_(self.proofsize_path)
                reset_folder_(self.proofstep_path)
                open(args.search_states, 'w').close()
        else:
            reset_folder_(self.proofsize_path)
            reset_folder_(self.proofstep_path)
        args.dec_names_path = 'data/train.names'
        args.pretrained_model = model_path
        args.use_value_function = use_value_function
        args.e = 8
        args.d = 512
        search_main(args)

        self.generate_dataset(k)

    def fine_tune(self, args, data_paths, model_path, k):
        reset_folder_('data/split/')
        args.raw = False
        split_file(data_paths, split_data_path='data/split/', num_pieces=100)
        args.retrieval=False
        args.raw_data_path = None
        args.data_feet_type = 'batched'
        args.epochs = 1
        args.output_dir = f'model_theta{k}/'
        args.pretrained_model = model_path
        train_main(args)

    def expert_iteration(self, num_iterate):
        """
        Use tactic and mix1 to get theta 0
        """
        print('============== Pre-training ==============')
        args = self.args
        # -- pretrain
        self.pretrain(args)

        # -- generate data for proofsize objective
        print('============== Generating data for proofsize objective ==============')
        model_path = 'model_theta0/final_model'
        use_value_function = False
        self.generate_new_proofsize_and_proofstep_data(self, args, model_path, use_value_function, 0)

        # -- boostraping
        for k in range(num_iterate):
            print(f'============== Expert iteration {k} ==============')
            print(f'============== Fine tuning {k} ==============')
            self.fine_tune(args, [f'data/generated/proofsize_{k}.txt', 
                            f'data/generated/proofstep_{k}.txt',
                            'data/train_proofstep.txt', 
                            'data/mix1.txt'], model_path, k)
            
            print(f'============== Generating proofsize {k} ==============')
            self.generate_new_proofsize_and_proofstep_data(self, args, 
                            f'model_theta{k}/final_model', True, k)

    def generate_dataset(self, k):
        files = os.listdir(self.proofsize_path)
        proofsize_out = open(f'data/generated/proofsize_{k}.txt', 'w')
        for f in files:
            fname = os.path.join(self.proofsize_path, f)
            print(f'Processing {fname}')
            df = pd.read_csv(fname)
            for _, rows in tqdm(df.iterrows()):
                decl_name = rows['decl_name']
                goal = rows['goal'].replace('\n', ' ').replace('\t', ' ')
                proofsize = rows['proofsize']

                line = 'DEC ' + decl_name + ' GOAL ' + goal + ' PROOFSIZE ' + proofsize
                
                proofsize_out.write(line + '\n')


        files = os.listdir(self.proofstep_path) 
        proofstep_out = open(f'data/generated/proofstep_{k}.txt', 'w')
        for f in files:
            fname = os.path.join(self.proofstep_path, f)
            print(f'Processing {fname}')
            df = pd.read_csv(fname)
            for _, rows in tqdm(df.iterrows()):
                decl_name = rows['decl_name']
                goal = rows['goal'].replace('\n', ' ').replace('\t', ' ')
                proofstep = rows['proofstep']

                line = 'DEC ' + decl_name + ' GOAL ' + goal + ' PROOFSTEP ' + proofstep
                
                proofstep_out.write(line + '\n')
        
        proofstep_out.close()
        proofstep_out.close()


    
if __name__ == '__main__':
    args = parser.parse_args()
    ExpertIteration(args).expert_iteration(10)

