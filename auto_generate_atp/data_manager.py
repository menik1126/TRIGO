import fileinput
from torch.utils.data import Dataset
from functools import partial

from transformers import DataProcessor
from utils import memmap
import pickle
import numpy as np
import os
import random
import torch
import json
from pathlib import Path
from copy import copy

import logging
logger = logging.getLogger()

class PACTDataBatchedWithRetrieval(Dataset):
    def __init__(self, args, tokenizer, file_index) -> None:
        self.args = args
        self.tokenizer = tokenizer
        self.n_ctx = args.n_ctx
        self.memory_size = args.memory_size,
        stat = json.loads(Path(args.processed_stats_json_path).read_text())
        self.num_chunks = stat['total_chunks']


        self.file_index = file_index
        
        chunks_shape =  (self.num_chunks, args.chunk_size)
        chunks_hs_shape = (self.num_chunks, args.chunk_size, 1024)
        knn_shape = (self.num_chunks, args.knn)

        self.get_chunks = partial(memmap, stat['chunks_memmap_path'], dtype = np.int32, shape = chunks_shape)
        self.get_hs_chunks = partial(memmap, stat['hidden_state_path'], dtype = np.float32, shape = chunks_hs_shape)
        self.get_knns = partial(memmap, stat['knn_memmap_path'], dtype = np.int32, shape = knn_shape)
        self.get_seq = pickle.load(open(args.seq_dict_memmap_path, 'rb'))

        with open(args.split_data_path + 'split_train_{}.txt'.format(file_index), 'r') as f:
            lines = f.readlines()

        self.data = lines
    
    def __len__(self):
        return len(self.data)
    
    def __getitem__(self, index):
        data = self.data[index]
        with self.get_hs_chunks() as chunks_hs_memmap, self.get_knns() as knns_memmap \
            , self.get_chunks() as chunks_memmap:
            chunk_id = self.get_seq[self.file_index][index]
            
            # chunk_ids = chunks_memmap[chunk_id]
            # data_s = self.tokenizer.decode(chunk_ids, skip_special_tokens=self.tokenizer.pad_token_id).strip()
            # length = min(len(data.strip()), len(data_s))
            
            # if data_s[:length] != data[:length]:
            #     print(data_s[:length])
            #     print(data[:length])
            knns = knns_memmap[chunk_id]
            
            # derive mask for no neighbors found (-1)

            no_neighbor_mask = knns == -1
            knns = np.maximum(knns, 0)

            # get neighbor and continuation chunks
            knn_chunks = chunks_memmap[knns]
            knn_hs_chunks = chunks_hs_memmap[knns]
            

            knn_chunks = np.where(~no_neighbor_mask[..., None], knn_chunks, self.tokenizer.pad_token_id)

            knn_hs_chunks = knn_hs_chunks.reshape(-1, 1024)
            knn_chunks = knn_chunks.reshape(-1)

            atten_mask = knn_chunks != self.tokenizer.pad_token_id

        # tokenize the sentence
        data = self.tokenizer.encode(data.strip(), max_length=self.n_ctx - 1, truncation=True)

        # -- add eos token to the end of the sentence
        data.append(self.tokenizer.eos_token_id)

        # -- pad to n_ctx length
        data = data + [self.tokenizer.pad_token_id] * (self.n_ctx - len(data))

        # --return tensor
        return torch.LongTensor(data), torch.from_numpy(knn_hs_chunks), torch.from_numpy(atten_mask)

class PACTDataBatched(Dataset):
    def __init__(self, args, tokenizer, file_index) -> None:
        self.args = args
        self.tokenizer = tokenizer
        self.n_ctx = args.n_ctx

        with open(args.split_data_path + 'split_train_{}.txt'.format(file_index), 'r') as f:
            lines = f.readlines()
        random.shuffle(lines)

        self.data = lines
    
    def __len__(self):
        return len(self.data)
    
    def __getitem__(self, index):
        data = self.data[index]

        data = data.strip() + ' <|endoftext|>'

        # tokenize the sentence
        data = self.tokenizer(data.strip(), max_length=self.n_ctx - 1, 
                            truncation=True, padding='max_length', return_tensors='pt')

        # -- add eos token to the end of the sentence
        # data.append(self.tokenizer.eos_token_id)

        # -- pad to n_ctx length
        # data = data + [self.tokenizer.pad_token_id] * (self.n_ctx - len(data))

        input_ids, attention_mask = data.input_ids.squeeze(), data.attention_mask.squeeze()
        labels = torch.where(input_ids != self.tokenizer.pad_token_id, input_ids, -100)

        # --return tensor
        return input_ids, attention_mask, labels


class PACTDataSlideWindow(Dataset):
    def __init__(self, args, tokenizer, file_index) -> None:
        self.args = args
        self.tokenizer = tokenizer
        n_ctx = args.n_ctx

        with open(args.tokenized_data_path + 'tokenized_train_{}.txt'.format(file_index), 'r') as f:
                line = f.read().strip()
        tokens = line.split()
        tokens = [int(token) for token in tokens]
        start_point = 0
        samples = []
        while start_point < len(tokens) - n_ctx:
            samples.append(tokens[start_point: start_point + n_ctx])
            start_point += args.stride
        if start_point < len(tokens):
            samples.append(tokens[len(tokens)-n_ctx:])
        random.shuffle(samples)

        self.data = samples
    
    def __len__(self):
        return len(self.data)
    
    def __getitem__(self, index):
        return torch.LongTensor(self.data[index])

class TestData(Dataset):
    def __init__(self, args, data_path, tokenizer) -> None:
        self.data_path = data_path
        with open(self.data_path, 'r') as f:
            self.lines = f.readlines()
        self.tokenizer = tokenizer
        self.n_ctx = args.n_ctx
    
    def __len__(self):
        return len(self.lines)

    def __getitem__(self, index):
        line = self.lines[index]

        tokens = self.tokenizer(line.strip(), max_length=self.n_ctx - 1, 
                    truncation=True, padding='max_length', return_tensors='pt')
        labels = tokens.input_ids.clone()

        # if 'PROOFSTEP' in labels, we only use token after 'PROOFSTEP' 
        # to calcualte ppl
        if 42135 in labels:
            labels[:, :torch.where(labels[0]==42135)[0].item() + 1] = -100
        labels[labels == self.tokenizer.pad_token_id] = -100
        return tokens.input_ids, tokens.attention_mask, labels

def get_test_dataloader(args, datapath, tokenizer, world_size, rank):
    dataset = TestData(args, datapath, tokenizer)
    dist_sampler = torch.utils.data.distributed.DistributedSampler(
            dataset=dataset,
            num_replicas=world_size,
            rank=rank)
    data_loader = torch.utils.data.DataLoader(
                dataset,
                sampler=dist_sampler,
                batch_size=args.batch_size,
                drop_last=True,
                pin_memory=True,
                num_workers=1)
    return data_loader


def get_dataloader_retro(args, tokenizer, file_index, world_size, rank):
    dataset = PACTDataBatchedWithRetrieval(args, tokenizer, file_index)
    dist_sampler = torch.utils.data.distributed.DistributedSampler(
            dataset=dataset,
            num_replicas=world_size,
            rank=rank)
    data_loader = torch.utils.data.DataLoader(
                dataset,
                sampler=dist_sampler,
                batch_size=args.batch_size,
                drop_last=True,
                pin_memory=True,
                num_workers=1)
    return data_loader

def get_dataloader_batced(args, tokenizer, file_index, world_size, rank):
    dataset = PACTDataBatched(args, tokenizer, file_index)
    dist_sampler = torch.utils.data.distributed.DistributedSampler(
            dataset=dataset,
            num_replicas=world_size,
            rank=rank)
    data_loader = torch.utils.data.DataLoader(
                dataset,
                sampler=dist_sampler,
                batch_size=args.batch_size,
                drop_last=True,
                pin_memory=True,
                num_workers=1)
    return data_loader

def get_dataloader_slide_window(args, tokenizer, file_index, world_size, rank):
    dataset = PACTDataSlideWindow(args, tokenizer, file_index)
    dist_sampler = torch.utils.data.distributed.DistributedSampler(
            dataset=dataset,
            num_replicas=world_size,
            rank=rank)
    data_loader = torch.utils.data.DataLoader(
                dataset,
                sampler=dist_sampler,
                batch_size=args.batch_size,
                drop_last=True,
                pin_memory=True,
                num_workers=1)
    return data_loader