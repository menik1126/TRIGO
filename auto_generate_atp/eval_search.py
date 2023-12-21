import argparse
from contextlib import redirect_stdout
import os
from pstats import Stats

import torch
from tactic_generator import TacticGenerator
from search_beam import ProofBeamSearch
from search import ProofSearch
from lean_server import LeanServer, LeanFatalError
import argparse
import multiprocessing
import torch.multiprocessing as mp

from utils import print

parser = argparse.ArgumentParser()
parser.add_argument(
    '--devices', type=str, nargs='+', default=['4', '5'],
    help='which devices to use on local machine')
parser.add_argument('--dec_names_path', default='data/test.names',
                    type=str, required=False, help='原始语料')
parser.add_argument('--search_states', default='data/search_state.txt',
                    type=str, required=False, help='保存搜索进度')
parser.add_argument('--pretrained_model', default='model0330/model_epoch1',
                    type=str, required=False, help='模型起点路径')
parser.add_argument('--model_type', default='gpt2-medium',
                    type=str, required=False, help='模型起点路径')
parser.add_argument('--temperature', default=1, type=float,
                    required=False, help='generation temperature')
parser.add_argument('--max_length', default=750, type=int,
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
parser.add_argument('--beam_size', default=1, type=int,
                    required=False, help='beam search size. If set to 1, it is equivalent to Greedy')
parser.add_argument('--use_beam_search', default=False,
                    action="store_true", help='whether use beam search or not. Default False')
parser.add_argument('--n_retry', default=0, type=int,
                    required=False, help='number of time regenerating the tactics when #e tactic is not applicable')
parser.add_argument('--try_intros', default=True, type=bool,
                    required=False, help='use `try {intros}` tactic for every proof after init search')
parser.add_argument('--use_value_function', default=True, type=bool,
                    required=False, help='use value function to evaluate goals')                    


def proof_search(rank, proofs, proof_states, shared_queue, args):
    print(f'{multiprocessing.current_process().name} started proofsearch')
    answers = {}
    print('Creating tactic generator...')
    import os
    os.environ['CUDA_VISIBLE_DEVICES'] = str(args.devices[rank].split(':')[-1])
    device = 'cuda' if torch.cuda.is_available() else 'cpu'
    tactic_generator = TacticGenerator(device, args.pretrained_model, args.model_type, args.max_length,
                                        args.temperature, args.topk, args.topp, args.repetition_penalty)

    print('Creating LEAN-gym server...')
    lean_server = LeanServer('lean')
    total_proofs = len(proofs)
    cnt = 0
    stats = {'error': 0, 'success': 0, 'init_faild': 0, 'queue empty': 0}
    for line in proofs:
        if line.strip() in proof_states:
            print(f'Skipping {line.strip()}')
            cnt += 1
            stats[proof_states[line.strip()]] += 1
            continue
        names = line.split()
        dec_names = names[0]
        namespaces = ' '.join(names[1:])
        # dec_names = "turing.TM2.stmts₁_supports_stmt_mono"
        # namespaces = 'turing.TM2 turing.TM2 turing relation turing.TM2.stmt turing.TM1 nat function turing.TM0.stmt turing.TM1.stmt'
        if args.use_beam_search:
            print(f"Using beam search! Beam size is {args.beam_size}")
            proofsearch = ProofBeamSearch(lean_server, tactic_generator, args.e,
                                  args.d, args.beam_size, dec_names, namespaces, args.n_retry,
                                  args.try_intros, args.use_value_function)
        else:
            proofsearch = ProofSearch(lean_server, tactic_generator, args.e,
                                          args.d, dec_names, namespaces, args.n_retry,
                                          args.try_intros, args.use_value_function)
        try:
            result = proofsearch.search()
        except LeanFatalError:
            result = "Lean fatal error"
            lean_server = LeanServer('lean')
        result_state = None
        if isinstance(result, list):
            print('\n\n')
            print('=' * 30, f'{multiprocessing.current_process().name} Search found!!!!!!!', '='*30)
            print(result)
            stats['success'] += 1
            result_state = 'success'
            print(stats)
            acc = stats["success"] / (cnt - stats["init_faild"] + 0.001)
            print(f'Process: {cnt / total_proofs:.3f}, acc: {acc:.3f}')
            print('=' * 30, '=====================', '='*30)
            print('\n\n')
        else:
            print('\n\n')
            print('=' * 30, f'{multiprocessing.current_process().name} Search Failed', '='*30)
            print(f'Reason: {result}')
            if 'Init search failed' == result:
                stats['init_faild'] += 1
                result_state = 'init_faild'
            elif 'Search queue empty.' == result:
                stats['queue empty'] += 1
                result_state = 'queue empty'
            else:
                stats['error'] += 1
                result_state = 'error'
            cnt += 1
            print(stats)
            acc = stats["success"] / (cnt - stats["init_faild"] + 0.001)
            print(f'Process: {cnt / total_proofs:.3f}, acc: {acc:.3f}')
            print('=' * 30, '=============', '='*30)
            print('\n\n')
        answers[line] = result
        # record the state 
        line = line.strip() + '-' + result_state
        shared_queue.put(line.strip())

    return answers


def main(args):
    print('args:\n' + args.__repr__())
    num_worker = len(args.devices)
    with open(args.dec_names_path, 'r') as f:
        proofs = f.readlines()
    division = len(proofs) / float(num_worker)
    splited_proofs = [proofs[int(round(
        division * i)): int(round(division * (i + 1)))] for i in range(num_worker)]

    states = {}
    if os.path.exists(args.search_states):
        with open(args.search_states, 'r') as f:
            lines = f.readlines()
        for line in lines:
            line = line.split('-')
            states[line[0].strip()] = line[1].strip()
    
    # This will create Process-1
    manager = mp.Manager()
    shared_queue = manager.Queue()
    
    # start the recorder `Process-2`
    recoder = mp.Process(target=record_finished_proofs, args=(shared_queue, args))
    recoder.start()

    processes = []
    # mp.set_start_method('spawn')
    for rank in range(num_worker):
        p = mp.Process(target=proof_search, args=(rank,
            splited_proofs[rank], states,  shared_queue, args))
        p.start()
        processes.append(p)
    for p in processes:
        p.join()
    
    # stop the recorder
    # TODO: not sure this will terminate the recorder properly when `ctrl-c` is used
    shared_queue.put('kill')
    recoder.join()


def record_finished_proofs(shared_queue, args):
    print(f'{multiprocessing.current_process().name} started record')
    with open(args.search_states, 'a') as f:
        while True:
            m = shared_queue.get()
            if m == 'kill':
                f.write('killed')
                break
            f.write(str(m) + '\n')
            f.flush()


if __name__ == '__main__':
    args = parser.parse_args()
    main(args)
