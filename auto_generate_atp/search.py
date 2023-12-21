from copy import copy
from multiprocessing.dummy import current_process
from queue import PriorityQueue, Queue
import logging
from lean_server import LeanServer
from utils import get_bucket
import pandas as pd
import os
import multiprocessing
from utils import print

logger = logging.getLogger()

class TreeNode:
    def __init__(self, val, children, parent, priority=0.0):
        self.val = val   # dict: tactic state returned by lean-gym
        self.depth = 0
        self.priority = priority     # logprob computed by the LM
        if children:
            self.children = children
        else:
            self.children = []
        self.parent = parent
        
        # marker for backtrack
        self.visited = False
    
    def __repr__(self) -> str:
        return str(self.val)

class ProofSearch:

    def __init__(self, 
                lean_server, 
                tactic_generator, 
                e, 
                d, 
                dec_name, 
                namespaces="",
                n_retry=0,
                try_intros=False,
                use_value_function=False):
        self.lean_server = lean_server
        self.tactic_generator = tactic_generator
        self.search_id = None
        self.tactic_state_id = None
        self.proof_tree = None
        self.search_queue = PriorityQueue()
        self.e = e
        self.d = d
        self.n_retry = n_retry
        self.try_intros = try_intros
        self.dec_name = dec_name
        self.namespaces = namespaces

        self.use_value_function = use_value_function

        self.proofsize_path = 'data/proofsize_tmp/'
        self.proofstep_path = 'data/proofstep_tmp/'
        if not os.path.exists(self.proofsize_path):
            os.mkdir(self.proofsize_path)
        if not os.path.exists(self.proofstep_path):
            os.mkdir(self.proofstep_path)

        self.tactic_state_history = set()

        self.__init_search(dec_name, namespaces)

    def __init_search(self, dec_name, namespaces):
        print(f'Init search: {dec_name} {namespaces}')
        search = self.lean_server.init_search(dec_name, namespaces)
        if not search['error'] is None:
            print(f'Init search failed.\n Error: {search["error"]}') 
        self.search_id = search['search_id']
        if self.try_intros:    # to macht the format of the training dataset, use intros 
            search = self.lean_server.run_tac(search_id=self.search_id,
                                    tactic_id=search['tactic_state_id'],
                                    tactic='try {intros}')

        init_node = TreeNode(search, None, None, 0)
        self.search_queue.put((0, init_node))
        self.proof_tree = init_node
        print(f'Init search: {dec_name} {namespaces} COMPLETE!')

    def __eval_tactics(self, tactics_state):
        # gpt get tactics text
        query_text = 'DEC ' + self.dec_name + ' GOAL ' + tactics_state.replace('\n', ' ').replace('\t',' ').strip() + ' PROOFSIZE'
        print(f'Query text: {query_text}')
        return self.tactic_generator.value_function(query_text)

    def __get_tactics(self, node):
        """
        Return a list of applicable TreeNode objects
        """
        val = node.val
        goal = val['tactic_state']

        # split goal with '\n', if one tactic state contains multiple goals, 
        # use only the first goal as actual goal for gpt-2 generation.
        goal = goal.split('\n')
        # TODO: verify if multiple goal existed, `k goals` is in the goals, and `case xxx`` in second line.
        if 'goals' in goal[0]:
            goal = goal[1:]
            if goal[0].startswith('case'):
                goal = goal[1:]
            # goal = goal[: goal.index('')]   # extract the first goal
        
        # TODO: is getting rid of this case is nessary, and will it cause other issue?
        if goal[0].startswith('case'):
            goal = goal[1:]
        goal = ' '.join(goal)

        
        # gpt get tactics text
        query_text = 'DEC ' + self.dec_name + ' GOAL ' + goal.replace('\n', ' ').replace('\t',' ').strip() + ' PROOFSTEP'
        print(f'Query text: {query_text}')
        tactics = self.tactic_generator.generate(query_text, self.e)    # list[(logprob:float, tactic:str)], length = deduplicated list of lenght self.e <= self.e
        
        # [print(f'Candidate Tactics: {logp} - {tactic}') for logp, tactic in tactics]
        return_list = []
        for (logp, t) in tactics:
            print(f"Generated tactic - {logp:.4f} - {t}")
            # Fix broken pipe error
            # generated tactic may contains strange charater that causes broken pipe error
            try:
                result = self.lean_server.run_tac(search_id=self.search_id,
                                    tactic_id=val['tactic_state_id'],
                                    tactic=t)       # dict returned by lean-gym
            except BrokenPipeError:
                continue
            print(f"lean_result - {result}")
            if result and result['error'] is None:
                if self.use_value_function:
                    logp = self.__eval_tactics(result['tactic_state'])

            if result and result['error'] is None:
                if result['tactic_state'] in self.tactic_state_history:
                    continue
                self.tactic_state_history.add(result['tactic_state'])
                last_proof_steps = copy(val['proof_steps'])
                last_proof_steps.append((logp, t))
                result['proof_steps'] = last_proof_steps
                cum_logp = 0
                for p, _ in result['proof_steps']:
                    cum_logp += p
                return_list.append(TreeNode(result, None, node, cum_logp))
        
        return return_list
    
    def __search(self, node, n_nodes=0):
        print('\n\n')
        goal_text = node.val["tactic_state"].replace("\n", " ")
        print(f'Searching Goal: {goal_text}')
        print(f'Previous Tactics: {node.val["proof_steps"]}')
        if n_nodes > self.d:
            return 'Maximun search depth reached'
        if node.val['tactic_state'] == 'no goals':
            return node.val['proof_steps']
        
        n_retry = 0
        while True:
            try:
                tactics = self.__get_tactics(node)
            except AssertionError as e:
                if str(e) == 'input query lenght exceed limit':
                    tactics = []
                    break
                return str(e)
            if len(tactics) > 0 or n_retry >= self.n_retry:
                break
            n_retry += 1
        
        for t in tactics:
            t.depth = node.depth + 1
            self.search_queue.put((-t.priority, t))
        node.children = tactics

        # check for success
        for t in tactics:
            if t.val['tactic_state'] == 'no goals':
                self.calculate_proofsize(t)
                return t.val['proof_steps']

        if not self.search_queue.empty():
            _, next_node = self.search_queue.get()
            return self.__search(next_node, n_nodes=n_nodes+1)
        else:
            return 'Search queue empty.'
    
    def calculate_proofsize(self, succes_node):
        proofsize = 1
        succes_node.visited = True
        current_node = succes_node.parent
        pre_node = succes_node
        proofsize_records = []
        proofstep_records = []

        # -- step 1: record every successful proofs
        while current_node is not None:
            proofsize_records.append({
                'decl_name': self.dec_name,
                'goal': current_node.val['tactic_state'].replace('\n', ' '),
                'proofsize': get_bucket(proofsize)
            })
            proofstep_records.append({
                'decl_name': self.dec_name,
                'goal': current_node.val['tactic_state'].replace('\n', ' '),
                'proofstep': pre_node.val['proof_steps'][-1][1]
            })
            proofsize += 1
            current_node.visited = True
            pre_node = current_node
            current_node = current_node.parent
        
        # -- step 2: 层序遍历，加入那些不成功的节点作为无限proofsize的
        q = Queue()
        q.put(self.proof_tree)
        while not q.empty():
            node = q.get()
            if not node.visited:
                proofsize_records.append({
                'decl_name': self.dec_name,
                'goal': node.val['tactic_state'].replace('\n', ' '),
                'proofsize': get_bucket(100000000)
            })
            node.visited = True
            for child in node.children:
                q.put(child)
        

        fname = f'{self.proofsize_path}{multiprocessing.current_process().name}_proofsize.csv'
        if not os.path.isfile(fname):
            pd.DataFrame(proofsize_records).to_csv(fname, header='column_names', index=None)
        else: # else it exists so append without writing the header
            pd.DataFrame(proofsize_records).to_csv(fname, mode='a', header=False, index=None)
        
        fname = f'{self.proofstep_path}{multiprocessing.current_process().name}_proofstep.csv'
        if not os.path.isfile(fname):
            pd.DataFrame(proofstep_records).to_csv(fname, header='column_names', index=None)
        else: # else it exists so append without writing the header
            pd.DataFrame(proofstep_records).to_csv(fname, mode='a', header=False, index=None)
            

    def search(self):
        if not self.search_id is None:
            _, first_node = self.search_queue.get()
            return self.__search(first_node)
        return 'Init search failed'
