from numpy import number
import torch
import torch.nn.functional as F
import os
import argparse
from tqdm import trange
from transformers import GPT2LMHeadModel, GPT2Tokenizer
from retro_model import MemoryLMHeadModel

import logging

logger = logging.getLogger()


class TacticGenerator:
    def __init__(self,
                 devices,
                 pretrained_model_path,
                 model_type='gpt2-medium',
                 length=1024,
                 temperature=1,
                 topk=0,
                 topp=0.0,
                 repetition_penalty=1.0):
        os.environ["CUDA_VISIBLE_DEVICES"] = str(devices)  # 此处设置程序使用哪些显卡
        self.length = length
        self.temperature = temperature

        # top-k and top-p sampling are not currently used
        self.topk = topk
        self.topp = topp
        self.repetition_penalty = repetition_penalty

        self.device = "cuda" if torch.cuda.is_available() else "cpu"

        print('Init tactic generator')
        self.tokenizer = GPT2Tokenizer.from_pretrained(model_type)
        # add special token
        self.tokenizer.add_special_tokens({'pad_token': '<|pad|>'})
        self.model = MemoryLMHeadModel.from_pretrained(pretrained_model_path)
        self.model.resize_token_embeddings(len(self.tokenizer))
        self.model.to(self.device)
        self.model.eval()

    def value_function(self, prefix_text):
        input_ids = self.tokenizer.encode(
            prefix_text, return_tensors='pt').to(self.device)
        
        # assert if input length is to long for generation, spare 10 token for generated tactic
        assert input_ids.size(1) < self.length - 10, 'input query lenght exceed limit'
        outputs = self.model(input_ids)
        next_token_logits = outputs[0][0, -1, :]
        # A B C D E F G H I J K
        INDEX = self.tokenizer.encode(' A B C D E F G H I J K')
        logits = next_token_logits[INDEX].softmax(dim=0)
        score = torch.FloatTensor([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]).to(self.device)
        return (logits * score).mean().item()



    def generate(self, prefix_text, num_sample):
        input_ids = self.tokenizer.encode(
            prefix_text, return_tensors='pt').to(self.device)
        
        # assert if input length is to long for generation, spare 10 token for generated tactic
        assert input_ids.size(1) < self.length - 10, 'input query lenght exceed limit'
        sample_outputs = self.model.generate(
            input_ids,
            do_sample=True,
            max_length=self.length,
            num_return_sequences=num_sample,
            temperature=self.temperature,
            output_scores=True,
            return_dict_in_generate=True,
            pad_token_id=self.tokenizer.eos_token_id
        )
        sequences = sample_outputs.sequences.cpu()
        scores = sample_outputs.scores
        logp_sequences = sequences[:, input_ids.size(1):]  # 去掉input部分
        # 处理一下score  32 100    ([32，1,  50270], [32, 50270],
        scores = [s.unsqueeze(1).cpu() for s in scores]   
        scores = torch.cat(scores, dim=1)        # [32, 100, 50270]
        scores = scores.softmax(dim=2).log() # log(p)
        logp_index = logp_sequences.reshape(num_sample, -1, 1)
        scores = scores.gather(2, logp_index).reshape(num_sample, -1)
        scores = scores * \
            (logp_sequences != self.tokenizer.convert_tokens_to_ids('<|endoftext|>'))
        scores = scores.nan_to_num(0).sum(1)

        # Add small random Gaussian noise to prevent priority queue errors
        scores = scores + 0.0001 * torch.randn_like(scores)

        scores = scores.tolist()

        result_set = set()
        result = []
        for i in range(num_sample):
            sample = sequences[i]
            text = self.tokenizer.decode(sample)
            if '<|endoftext|>' in text:
                text = text[text.rfind('PROOFSTEP') +
                          9: text.index('<|endoftext|>')].strip()
            else:
                text = text[text.rfind('PROOFSTEP') + 9:].strip()
            # # TODO: why this is exists? model thing
            # if 'proofstep' in text:
            #     text = text[text.rfind('proofstep') + 9:].strip()

            if text not in result_set:
                result_set.add(text)
                result.append((scores[i], text))

        return result
    
    def share_memory(self):
        self.model.share_memory()
