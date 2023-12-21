import torch
import os
from tqdm import tqdm
from pathlib import Path
import torch
import torch.distributed as dist
import random

from logging import getLogger
from contextlib import contextmanager
import numpy as np
from shutil import rmtree, copytree
import multiprocessing as mp
import builtins

logger = getLogger()
BUCKETS = list('ABCDEFGHIJK')

def build_files_slide_window(data_path, tokenized_data_path, num_pieces, full_tokenizer, min_length):
    with open(data_path, 'r', encoding='utf8') as f:
        print('reading lines')
        lines = f.readlines()
        lines = [line.replace('\n', ' <|endoftext|> ') for line in lines]  # 用[SEP]表示换行, 段落之间使用SEP表示段落结束
    all_len = len(lines)
    if not os.path.exists(tokenized_data_path):
        os.mkdir(tokenized_data_path)
    for i in tqdm(range(num_pieces)):
        sublines = lines[all_len // num_pieces * i: all_len // num_pieces * (i + 1)]
        if i == num_pieces - 1:
            sublines.extend(lines[all_len // num_pieces * (i + 1):])  # 把尾部例子添加到最后一个piece
        sublines = [full_tokenizer.tokenize(line) for line in sublines if
                    len(line) > min_length]  # 只考虑长度超过min_length的句子
        sublines = [full_tokenizer.convert_tokens_to_ids(line) for line in sublines]
        full_line = []
        for subline in sublines:
            full_line.append(full_tokenizer.convert_tokens_to_ids('<|endoftext|>'))  # 文章开头添加MASK表示文章开始
            full_line.extend(subline)
            full_line.append(full_tokenizer.convert_tokens_to_ids('<|endoftext|>'))  # 文章之间添加CLS表示文章结束
        with open(tokenized_data_path + 'tokenized_train_{}.txt'.format(i), 'w') as f:
            for id in full_line:
                f.write(str(id) + ' ')
    logger.info('finish')

def split_file(data_paths, split_data_path, num_pieces):
    all_lines = []
    for data_path in data_paths:
        with open(data_path, 'r', encoding='utf8') as f:
            print('reading lines')
            all_lines.extend(f.readlines())
    random.shuffle(all_lines)
    lines = all_lines
    all_len = len(lines)
    if not os.path.exists(split_data_path):
        os.mkdir(split_data_path)
    for i in tqdm(range(num_pieces)):
        sublines = lines[all_len // num_pieces * i: all_len // num_pieces * (i + 1)]
        if i == num_pieces - 1:
            sublines.extend(lines[all_len // num_pieces * (i + 1):])  # 把尾部例子添加到最后一个piece
        with open(split_data_path + 'split_train_{}.txt'.format(i), 'w') as f:
            for subline in sublines:
                f.write(subline)
    logger.info('finish')



def init_distributed(port=40101, rank_and_world_size=(None, None)):

    if dist.is_available() and dist.is_initialized():
        return dist.get_world_size(), dist.get_rank()

    rank, world_size = rank_and_world_size
    os.environ['MASTER_ADDR'] = 'localhost'

    if (rank is None) or (world_size is None):
        try:
            world_size = int(os.environ['SLURM_NTASKS'])
            rank = int(os.environ['SLURM_PROCID'])
            os.environ['MASTER_ADDR'] = os.environ['HOSTNAME']
        except Exception:
            logger.info('distributed training not available')
            world_size, rank = 1, 0
            return world_size, rank

    try:
        os.environ['MASTER_PORT'] = str(port)
        torch.distributed.init_process_group(
            backend='nccl',
            world_size=world_size,
            rank=rank)
    except Exception:
        world_size, rank = 1, 0
        logger.info('distributed training not available')

    return world_size, rank


@contextmanager
def memmap(*args, **kwargs):
    pointer = np.memmap(*args, **kwargs)
    yield pointer
    del pointer

def reset_folder_(p):
    path = Path(p)
    rmtree(path, ignore_errors = True)
    path.mkdir(exist_ok = True, parents = True)

def copy_folder_(src, dest):
    src = Path(src)
    dest = Path(dest)
    copytree(src, dest, dirs_exist_ok=True)

def get_bucket(proofsize):
    # -- get bucket
    bucket = None
    # -- inifinte proofsize
    if proofsize > 1000:
        bucket = BUCKETS[0]
        return bucket
    if proofsize > 20:
        bucket = BUCKETS[1]
    else:
        # linearly projecting proofsize under 20 in 9 buckets: 20 / 9 = 2.222...
        bucket = BUCKETS[int(10 - proofsize // 2.222)]
    return bucket


def print(*objs, **kwargs):
    my_prefix = f'{mp.current_process().name} :: '
    builtins.print(my_prefix, *objs, **kwargs)

def get_goals(state):
    '''
    get goal list of the tactic state
    if tactic state has multiple goals, it should be like:
        X goals\n
        goal1\n\n
        goal2\n\n
        ...  \n\n
        goalX
    return [goal1, goal2, ..., goalX] (the head 'X goals' is also removed)
    '''
    goals = state.split("\n\n")
    if len(goals) > 1:
        goals_title = f"{len(goals)} goals\n"
        if goals[0].startswith(goals_title):
            goals[0] = goals[0][len(goals_title):]
    return goals

def remove_case_head(goal):
    ''' Remove the first case xxx part of goal'''
    if goal.startswith("case"):
        split_goal = goal.split("\n")[1:]
        return "\n".join(split_goal)
    else:
        return goal
