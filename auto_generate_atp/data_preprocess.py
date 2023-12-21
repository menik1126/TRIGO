from argparse import Namespace
from cmath import exp
from tokenize import Decnumber
from sqlalchemy import outparam
from transformers import GPT2Tokenizer, GPT2LMHeadModel
import os
import pandas as pd
from tqdm import tqdm
from lean_server import LeanServer
import numpy as np

def process_proofstep_data():
    data_df = pd.read_csv('datasets/cleaned_training_data/data_and_metadata.csv')
    data_df = data_df[~data_df['cleaned_goal'].isna()]
    train_file = open('data/train_proofstep.txt', 'w')
    valid_file = open('data/valid.txt', 'w')
    test_file = open('data/test.txt', 'w')
    for _, row in tqdm(data_df.iterrows()):
        goal = row['cleaned_goal'].replace('\n', ' ').replace('\t',' ').strip()
        tactic = row['human_tactic_code'].replace('\n', ' ').replace('\t',' ').strip()
        dec_name = row['decl_name'].replace('\n', ' ').replace('\t',' ').strip()

        line = 'DEC ' + dec_name + ' GOAL ' + goal + ' PROOFSTEP ' + tactic
        
        if row['split'] == 'train':
            train_file.write(line + '\n')
        elif row['split'] == 'test':
            test_file.write(line + '\n')
        elif row['split'] == 'valid':
            valid_file.write(line + '\n')
        else:
            print('not in split!')


def proccess_src_and_tgt(src_file, tgt_file, out_file):
    
    output = open(out_file, 'w')
    with open(f'datasets/cleaned_training_data/{src_file}') as src:
        with open(f'datasets/cleaned_training_data/{tgt_file}') as tgt:
            src_iter = iter(src)
            tgt_iter = iter(tgt)
            i = 0
            try:
                while True:
                    src_line = next(src_iter)
                    tgt_line = next(tgt_iter)
                    new_line = 'GOAL ' + src_line.replace('\n', ' ').replace('\t',' ').strip() + ' PROOFSTEP ' + tgt_line.replace('\n', ' ').replace('\t',' ').strip()
                    output.write(new_line + '\n')
                    print(f'\r{i}',end='')
                    i += 1
            except StopIteration:
                print('finished')

# match_proofstep_data()

process_proofstep_data()

# dataset = 'train'
# proccess_src_and_tgt(f'{dataset}.src', f'{dataset}.tgt', f'data/{dataset}.txt')

# dataset = 'valid'
# proccess_src_and_tgt(f'{dataset}.src', f'{dataset}.tgt', f'data/{dataset}.txt')

# dataset = 'test'
# proccess_src_and_tgt(f'{dataset}.src', f'{dataset}.tgt', f'data/{dataset}.txt')


# os.system('cp datasets/cleaned_training_data/test.names data/test.names')
# os.system('cp datasets/cleaned_training_data/valid.names data/valid.names')