from distutils.command.build import build
import json
import os
from tokenize import Decnumber
from utils import memmap, reset_folder_
from pathlib import Path
import numpy as np
from einops import rearrange
from transformers import GPT2Tokenizer, GPT2Model
import torch
import pickle
from nltk.translate.bleu_score import sentence_bleu, SmoothingFunction

TMP_PATH = Path('./data/retrieval/.tmp')
INDEX_FOLDER_PATH = TMP_PATH / '.index'
EMBEDDING_TMP_SUBFOLDER = 'embeddings'
MODEL_EMBEDED_DIM = 1024

def range_chunked(max_value, *, batch_size):
    counter = 0
    while counter < max_value:
        curr = counter + batch_size
        curr = min(curr, max_value)
        yield slice(counter, curr)
        counter = curr

def faiss_read_index(path):
    import faiss
    return faiss.read_index(str(path), faiss.IO_FLAG_MMAP | faiss.IO_FLAG_READ_ONLY)

class Retrieval:
    def __init__(
        self,
        tokenizer,
        model,
        args
    ):
        self.tokenizer = tokenizer
        self.model = model
        self.args = args

        self.force_reprocess = args.reprocess_retrieval
        self.documents_path = args.split_data_path
        self.chunks_memmap_path = args.chunks_memmap_path
        self.seq_dict_memmap_path = args.seq_dict_memmap_path
        self.chunk_size = args.chunk_size
        self.max_chunks = args.max_chunks
        self.batch_size = args.retrieval_batch_size
        self.processed_stats_json_path = args.processed_stats_json_path
        self.knn = args.knn

        self.embedding_path = f'{self.chunks_memmap_path}.embedded'
        self.hidden_state_path = f'{self.chunks_memmap_path}.hidden_state'

        # store the processed training data statistics
        # number of chunks, number of sequences

        if not os.path.exists(self.processed_stats_json_path) or self.force_reprocess:
            stats = {}
            total_chunks = self._text_folder_to_chunks_()
            stats['total_chunks'] = total_chunks
            with open(self.processed_stats_json_path, 'w') as f:
                json.dump(stats, f)

        self.stats = json.loads(Path(self.processed_stats_json_path).read_text())
        self.num_chunks = self.stats['total_chunks']
        self._chunks_to_precalculated_knn_(self.knn)

    def _chunks_to_precalculated_knn_(
        self, 
        num_nearest_neighbors,
        index_file='knn.index', 
        embed_dim=MODEL_EMBEDED_DIM,
        index_infos_file = 'index_infos.json',
        num_extra_neighbors = 100,
        max_rows_per_file = 500,
        ):
        chunk_path = Path(self.chunks_memmap_path)
        knn_path = chunk_path.parents[0] / f'{chunk_path.stem}.knn{chunk_path.suffix}'
        index_path = INDEX_FOLDER_PATH / index_file

        # early return knn path and faiss index
        # unless if force_reprocess is True
        if 'knn_memmap_path' in self.stats and not self.force_reprocess:
            print(f'preprocessed knn found at {str(knn_path)}, faiss index reconstituted from {str(index_path)}')
            index = faiss_read_index(index_path)
            return knn_path, index
        
        # reset_folder_(INDEX_FOLDER_PATH)

        # -- step 1 get embed representation for each chunk
        embed_shape = (self.num_chunks, embed_dim)
        hidden_state_shape = (self.num_chunks, self.chunk_size, embed_dim)
        chunks_shape = (self.num_chunks, self.chunk_size)

        if 'chunks_memmap_path' not in self.stats or self.force_reprocess:
            with memmap(self.chunks_memmap_path, shape = chunks_shape, dtype = np.int32) as chunks\
                , memmap(self.embedding_path, shape = embed_shape, dtype = np.float32, mode = 'w+') as embeddings\
                , memmap(self.hidden_state_path, shape=hidden_state_shape, dtype = np.float32, mode = 'w+') as hidden_states:

                for dim_slice in range_chunked(self.num_chunks, batch_size = self.batch_size):
                    batch_chunk_npy = chunks[dim_slice]
                    batch_chunk = torch.from_numpy(batch_chunk_npy)
                    batch_embed, hs = self._model_embed(batch_chunk)

                    embeddings[dim_slice] = batch_embed.detach().cpu().numpy()
                    hidden_states[dim_slice] = hs.detach().cpu().numpy()
                    print(f'embedded {dim_slice.stop} / {self.num_chunks}')
            self.stats['hidden_state_path'] = self.hidden_state_path
            self.stats['chunks_memmap_path'] = self.chunks_memmap_path
            with open(self.processed_stats_json_path, 'w') as f:
                json.dump(self.stats, f)
            
        
        # -- step 2 memmap_file_to_chunks
        if 'chunked_embeddings_path' not in self.stats or self.force_reprocess:
            rows = self.num_chunks
            with memmap(self.embedding_path, shape=embed_shape, dtype = np.float32, mode='r') as f:
                root_path = TMP_PATH / EMBEDDING_TMP_SUBFOLDER
                reset_folder_(root_path)

                for ind, dim_slice in enumerate(range_chunked(rows, batch_size = max_rows_per_file)):
                    filename = root_path / f'{ind:05d}.npy'
                    np.save(str(filename), f[dim_slice])
                    print(f'saved {str(filename)}')
            self.stats['chunked_embeddings_path'] = str(root_path)
            with open(self.processed_stats_json_path, 'w') as f:
                json.dump(self.stats, f)
            
        
        # --step 3 index embeddings
        if 'index_path' not in self.stats or self.force_reprocess:
            chunked_embeddings_path = TMP_PATH / EMBEDDING_TMP_SUBFOLDER
            reset_folder_(INDEX_FOLDER_PATH)
            from autofaiss import build_index

            build_index(
                embeddings = str(chunked_embeddings_path),
                index_path = str(index_path),
                index_infos_path = str(INDEX_FOLDER_PATH / index_infos_file),
                metric_type = "l2",
                max_index_memory_usage = "1G",
                current_memory_available = "50G",
                should_be_memory_mappable = True,
                use_gpu = False,
            )
            self.stats['index_path'] = str(index_path)
            with open(self.processed_stats_json_path, 'w') as f:
                json.dump(self.stats, f)
        

        # -- step 4 get knn
        if 'knn_memmap_path' not in self.stats or self.force_reprocess:
            index = faiss_read_index(index_path)
            embeddings = np.memmap(self.embedding_path, shape = embed_shape, dtype = np.float32, mode = 'r')
            chunks_memmap = np.memmap(self.chunks_memmap_path, shape = (self.num_chunks, self.chunk_size), dtype = np.int32, mode = 'r')
            total_neighbors_to_fetch = num_extra_neighbors + num_nearest_neighbors + 1

            with memmap(knn_path, shape = (self.num_chunks, num_nearest_neighbors), dtype = np.int32, mode = 'w+') as knns:

                for dim_slice in range_chunked(self.num_chunks, batch_size = max_rows_per_file):
                    query_vector = embeddings[dim_slice]

                    distances, indices = index.search(query_vector, k = total_neighbors_to_fetch)
                    
                    # remove neigbours from the same proof
                    indices_from_same_proof = np.zeros_like(indices)
                    ori_chunks = chunks_memmap[dim_slice]
                    for i, idx in enumerate(indices):
                        chunks = chunks_memmap[idx]
                        ori_chunk = ori_chunks[i]
                        # 10351 == ` GO`` for ` GOAL`
                        dec_name = ori_chunk[:np.where(ori_chunk == 10351)[0][0]]
                        for j, chunk in enumerate(chunks):
                            chunk_dec_name = chunk[:np.where(chunk == 10351)[0][0]]
                            if np.array_equal(dec_name, chunk_dec_name):
                                indices_from_same_proof[i, j] = 1
                    
                    indices = np.where(indices_from_same_proof, -1, indices)
                    distances = np.where(indices_from_same_proof, 1e3, distances)
                    indices = np.take_along_axis(indices, np.argsort(distances, axis = 1), axis = 1)

                    # store nearest neighbors to knn memmap
                    knns[dim_slice] = indices[:, :num_nearest_neighbors]

                    print(f'knns calculated for {dim_slice.stop} / {self.num_chunks}')
            
            self.stats['knn_memmap_path'] = str(knn_path)
            with open(self.processed_stats_json_path, 'w') as f:
                json.dump(self.stats, f)


        print(f'knn saved to {knn_path}')
        return knn_path, index_path
        
    def _tokenize(self, texts, add_special_tokens = True):
        if not isinstance(texts, (list, tuple)):
            texts = [texts]

        encoding = self.tokenizer.batch_encode_plus(
            texts,
            add_special_tokens = add_special_tokens,
            padding = True,
            truncation = True,
            max_length = self.chunk_size,
            return_tensors = 'pt'
        )
        return encoding
    
    @torch.no_grad()
    def _model_embed(self, token_ids, eps = 1e-8):

        atten_mask = token_ids != self.tokenizer.pad_token_id
        
        token_ids = token_ids.to(self.model.device)
        atten_mask = atten_mask.to(self.model.device)

        outputs = self.model(
            input_ids = token_ids,
            attention_mask = atten_mask,
            output_hidden_states = True
        )

        hidden_state = outputs.hidden_states[-1]
        atten_mask = rearrange(atten_mask, 'b n -> b n 1')

        numer = (hidden_state * atten_mask).sum(dim = 1)
        denom = atten_mask.sum(dim = 1)
        masked_mean =  numer / (denom + eps)
        return masked_mean, outputs.hidden_states[17]


    def _doc_text_to_chunks_and_seq_indices(self, doc_text):
        doc_text = doc_text.split('\n')[:-1]
        # TODO: Delete the tactic?
        ids = self._tokenize(doc_text)
        return ids.input_ids

    
    def _text_folder_to_chunks_(self):
        paths = sorted([*Path(self.documents_path).glob('*.txt')])

        total_chunks = 0

        chunks_shape = (self.max_chunks, self.chunk_size)
        seq_dict = {}

        with memmap(self.chunks_memmap_path, shape = chunks_shape, dtype = np.int32, mode = 'w+') as chunks_memmap: 
            for path in paths:
                print(f'processing {path}')
                fnum = int(str(path)[str(path).rfind('_') + 1:-4])
                chunks = self._doc_text_to_chunks_and_seq_indices(path.read_text())
                
                doc_chunk_len = chunks.shape[0]
                chunks_memmap[total_chunks:(total_chunks + doc_chunk_len)] = chunks.numpy()
                seq_dict[fnum] = list(range(total_chunks, total_chunks + doc_chunk_len))
                total_chunks += doc_chunk_len
        
        pickle.dump(seq_dict, open(self.seq_dict_memmap_path, 'wb'))

        return total_chunks

    def benchmark_retrival(self):
        if 'benchmark_bleu_path' in self.stats:
            return None
        benchmark_bleu_path = f'{self.chunks_memmap_path}.bleu'
        chunks_shape =  (self.num_chunks, self.chunk_size)
        knns_shape = (self.num_chunks, self.knn)
        cc = SmoothingFunction()
        chunks_memmap = np.memmap(self.stats['chunks_memmap_path'], shape = chunks_shape, dtype=np.int32, mode='r')
        knns_memmap = np.memmap(self.stats['knn_memmap_path'], shape=knns_shape, dtype=np.int32, mode='r' )
        self.bleus = np.memmap(benchmark_bleu_path, shape = (self.num_chunks), dtype=np.float32, mode='w+')
        for dim_slice in range_chunked(self.num_chunks, batch_size = 500):
            knns = knns_memmap[dim_slice]
            ori_chunks = chunks_memmap[dim_slice]
            bleu_local = []
            for i in range(knns.shape[0]):
                ori_tactic = self.tokenizer.decode(ori_chunks[i], skip_special_tokens=self.tokenizer.pad_token_id)
                if 'PROOFSTEP' in ori_tactic:
                    ori_tactic = ori_tactic[ori_tactic.index('PROOFSTEP')+9:].strip()
                    if len(ori_tactic) == 0:
                        bleu_local.append(-1)
                        continue
                else:
                    bleu_local.append(-1)
                    continue
                tactics = []
                input_ids = chunks_memmap[knns[i]]
                for idx, input_id in enumerate(input_ids):
                    if knns[i][idx] == -1:
                        continue
                    tactic = self.tokenizer.decode(input_id, skip_special_tokens=self.tokenizer.pad_token_id)
                    if 'PROOFSTEP' in tactic:
                        tactic = tactic[tactic.find('PROOFSTEP')+9:].strip()
                        if len(tactic) > 0:
                            tactics.append(tactic)
                if len(tactics) == 0:
                    bleu_local.append(-1)
                    continue
                references = self.tokenizer(tactics).input_ids
                candidate = self.tokenizer.encode(ori_tactic)
                bleu = sentence_bleu(references, candidate, smoothing_function=cc.method1)
                bleu_local.append(bleu)
            self.bleus[dim_slice] = np.asarray(bleu_local)
            print(f'benchmark calculated for {dim_slice.stop} / {self.num_chunks}, \
                    bleu: {self.bleus[dim_slice][self.bleus[dim_slice] != -1].mean()}, \
                    count: {self.bleus[dim_slice][self.bleus[dim_slice] != -1].shape[0]}')
        print(f'avg bleu {self.bleus[self.bleus != -1].mean()}')
        self.stats['benchmark_bleu_path'] = benchmark_bleu_path
        with open(self.processed_stats_json_path, 'w') as f:
            json.dump(self.stats, f)


# if __name__=='__main__':
#     tokenizer = GPT2Tokenizer.from_pretrained('gpt2-medium')
#     tokenizer.add_special_tokens({'pad_token': '<|pad|>'})
#     model = GPT2Model.from_pretrained('gpt2-medium').to('cuda:6')
#     embedding_layer = model.resize_token_embeddings(len(tokenizer))
#     r = Retrieval(
#         tokenizer=tokenizer,
#         model=model,
#         reprocess_retrieval=True,
#         documents_path='data/split',
#         knn=2,
#         chunks_memmap_path='data/retrieval/train.chunks.dat',
#         seq_dict_memmap_path='data/retrieval/train.seq_dict.dat',
#         max_chunks = 1_000_000,                        # maximum cap to chunks
#         max_seqs = 100_000,                            # maximum seqs
#         knn_extra_neighbors = 100,                     # num extra neighbors to fetch
#         # max_index_memory_usage = '100m',
#         # current_memory_available = '1G'
#         processed_stats_json_path = 'data/retrieval/processed-stats.json',
#         faiss_index_filename = 'data/retrieval/knn.index',
#     )
    
