from copy import copy
from multiprocessing.dummy import current_process
from queue import Queue
import logging
from lean_server import LeanServer
from utils import get_bucket
import pandas as pd
import os
import multiprocessing
from utils import print, get_goals, remove_case_head
import math

logger = logging.getLogger()

class HyperEdge:
    def __init__(self, tactic, children_list, parent, priority=0.0, const_exp = 1.0):
        self.tactic = tactic
        self.total_value = 0.0  #W
        self.visit_count = 0  #N
        self.virtual_count = 0  #VC
        self.children_list = children_list
        self.parent = parent
        self.const_exp = const_exp
        self.priority = priority  # prob computed by the LM todo(sjh): check we use prob instead of logprob here

    def update_value(self, to_update):
        self.total_value += to_update
        self.visit_count += 1
        self.parent.visit_total += 1
        self.virtual_count -= 1

    def get_puct(self):
        C = self.visit_count + self.virtual_count
        Q = 0.5 / max(1, C) if self.visit_count == 0 else self.total_value / C  #todo(sjh): implement t solving for g
        return Q + self.const_exp * self.priority * math.sqrt(self.parent.visit_total) / (1+C)

    def __repr__(self) -> str:
        return str(self.tactic)


class HyperTreeNode:
    def __init__(self, val, children, parent):
        self.val = val  # dict: tactic state returned by lean-gym
        goal_list = get_goals(val['tactic_state'])
        self.first_goal = goal_list[0]
        self.other_goals = goal_list[1:]
        self.edges = []  #all expanded edges from this node
        self.selected_edge = None  #the edge chosen in the selection phase
        self.depth = 0
        self.is_solved = False
        self.last_n_node = -1
        self.visit_total = 0
        if children:
            self.children = children
        else:
            self.children = []
        self.parent = parent

        # marker for backtrack
        self.visited = False
        self.expanded = False

    def __repr__(self) -> str:
        return str(self.val)

    def add_edge(self, edge):
        self.edges.append(edge)

class ProofHyperTreeSearch:

    def __init__(self,
                 lean_server,
                 tactic_generator,
                 e,
                 d,
                 dec_name,
                 namespaces="",
                 n_retry=0,
                 try_intros=False,
                 use_value_function=False,
                 use_hyper_tree=False):
        self.lean_server = lean_server
        self.tactic_generator = tactic_generator
        self.search_id = None
        self.tactic_state_id = None
        self.proof_tree = None
        self.e = e
        self.d = d
        self.n_retry = n_retry
        self.try_intros = try_intros
        self.dec_name = dec_name
        self.namespaces = namespaces

        self.use_value_function = use_value_function
        self.use_hyper_tree = use_hyper_tree

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
        if self.try_intros:  # to macht the format of the training dataset, use intros
            search = self.lean_server.run_tac(search_id=self.search_id,
                                              tactic_id=search['tactic_state_id'],
                                              tactic='try {intros}')

        init_node = HyperTreeNode(search, None, None)
        self.proof_tree = init_node
        print(f'Init search: {dec_name} {namespaces} COMPLETE!')

    def __MaintainSolved(self, node):
        if node.parent is None:
            return
        sibling_list = node.parent_edge.children_list
        for sib in sibling_list:
            if not sib.is_solved:
                return
        node.parent.is_solved = True
        self.__MaintainSolved(node.parent)

    def __eval_tactics(self, tactics_state):
        # gpt get tactics text
        query_text = 'DEC ' + self.dec_name + ' GOAL ' + tactics_state.replace('\n', ' ').replace('\t',
                                                                                                  ' ').strip() + ' PROOFSIZE'
        print(f'Query text: {query_text}')
        return self.tactic_generator.value_function(query_text)

    def __get_tactics(self, node):
        """
        Return a list of applicable HyperEdges
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
        query_text = 'DEC ' + self.dec_name + ' GOAL ' + goal.replace('\n', ' ').replace('\t',
                                                                                         ' ').strip() + ' PROOFSTEP'
        # print(f'Query text: {query_text}')
        tactics = self.tactic_generator.generate(query_text,
                                                 self.e)  # list[(logprob:float, tactic:str)], length = deduplicated list of lenght self.e <= self.e

        # [print(f'Candidate Tactics: {logp} - {tactic}') for logp, tactic in tactics]
        return_list = []
        for (logp, t) in tactics:
            # print(f"Generated tactic - {logp:.4f} - {t}")
            # Fix broken pipe error
            # generated tactic may contains strange charater that causes broken pipe error
            try:
                result = self.lean_server.run_tac(search_id=self.search_id,
                                                  tactic_id=val['tactic_state_id'],
                                                  tactic=t)  # dict returned by lean-gym
            except BrokenPipeError:
                continue
            # print(f"lean_result - {result}")
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
                # cum_logp = 0  #todo(sjh): check if accumulated logprob is needed?
                # for p, _ in result['proof_steps']:
                #     cum_logp += p
                if self.use_hyper_tree:
                    goals = get_goals(result["tactic_state"])
                    _tactic_id = result['tactic_state_id']
                    child_node_list = []
                    for goal_id, goal in enumerate(goals):
                        # goal = remove_case_head(goal) todo(sjh): shared nodes
                        # if goal in self.goal2node:
                        #     child_node = self.goal2node[goal]
                        #     child_node.parent = node
                        # else:
                        sub_result = self.lean_server.run_tac(search_id=self.search_id,
                                                          tactic_id=_tactic_id,
                                                          tactic=f"tactic.rotate_left {goal_id}")  # rotate subgoal_i to the first
                        child_node = HyperTreeNode(sub_result, None, node)
                        child_node_list.append(child_node)
                    _edge = HyperEdge(t, child_node_list, node, logp)
                    for child in child_node_list:
                        child.parent_edge = _edge
                else:
                    child_node = HyperTreeNode(result, None, node)
                    if result["tactic_state"] == "no goals":
                        node.is_solved = True
                        self.__MaintainSolved(node)
                        if self.proof_tree.is_solved:
                            self.proof_tree.last_solved = child_node
                    _edge = HyperEdge(t, [child_node], node, logp)  #todo(sjh): check solved
                    child_node.parent_edge = _edge
                return_list.append(_edge)

        return return_list

    def __select(self, n_nodes):
        to_explore = Queue()
        leaf_nodes = []
        self.proof_tree.last_n_node = n_nodes
        to_explore.put(self.proof_tree)
        while not to_explore.empty():
            select_node = to_explore.get()
            if not select_node.expanded:  #unexpanded
                select_node.selected_edge = None
                leaf_nodes.append(select_node)
                continue
            if len(select_node.edges) == 0:
                continue
            #this is an internal node, select the best tactic according to PUCT
            max_puct = 0.0
            max_edge = None
            for edge in select_node.edges:
                edge_children = edge.children_list
                is_circle = False  #check if tactic leads to circle; last_n_node mark the last visit round
                for edge_child in edge_children:
                    if edge_child.last_n_node == n_nodes:
                        is_circle = True
                        break
                if is_circle:
                    continue
                puct = edge.get_puct()
                if puct > max_puct:
                    max_puct = puct
                    max_edge = edge

            #select (select_node, max_edge)
            select_node.selected_edge = max_edge
            max_edge.virtual_count += 1
            children_list = max_edge.children_list

            for child in children_list:
                child.last_n_node = n_nodes
                child.parent = select_node
                to_explore.put(child)
        return leaf_nodes

    def __expand(self, leaf_nodes):
        have_unexpanded = False
        for leaf in leaf_nodes:
            if leaf.expanded:
                continue
            have_unexpanded = True
            n_retry = 0
            while True:
                try:
                    tactics = self.__get_tactics(leaf)
                except AssertionError as e:
                    if str(e) == 'input query lenght exceed limit':
                        tactics = []
                        break
                    return str(e)
                if len(tactics) > 0 or n_retry >= self.n_retry:
                    break
                n_retry += 1

            leaf.edges = tactics
            leaf.expanded = True
            for edge in tactics:
                leaf.children += edge.children_list
        return have_unexpanded

    def __backprop(self, back_node):
        assert back_node.expanded
        if back_node.selected_edge is None:  #this is a leaf node
            if back_node.is_solved:
                return 1.0
            edges = back_node.edges
            if len(edges) == 0: #no valid edge
                return 0.0
            max_p = max([edge.priority for edge in edges])
            return max_p
        selected_edge = back_node.selected_edge
        # update (back_node, selected_edge)
        children_list = selected_edge.children_list
        to_update = 1.0
        for child in children_list:
            VT_g = self.__backprop(child)
            to_update *= VT_g
        selected_edge.update_value(to_update)
        return to_update

    def __search(self, n_nodes=0):
        # Monte Carlo Tree Search todo(sjh): support HyperTree Proof Search
        if n_nodes > self.d:
            print('Maximun search depth reached')
            return 'Maximun search depth reached'
        print("=" * 5, n_nodes, "="*5)
        leaf_nodes = self.__select(n_nodes)
        for leaf in leaf_nodes:
            print(leaf)
        print("leaf ends")
        have_unexpanded = self.__expand(leaf_nodes)
        if not have_unexpanded:
            print('Search queue empty.')
            return 'Search queue empty.'
        self.__backprop(self.proof_tree)
        if self.proof_tree.is_solved:
            print("success!!!!!!!!")
            self.calculate_proofsize(self.proof_tree.last_solved)
            return self.proof_tree.last_solved.val['proof_steps']
        return self.__search(n_nodes=n_nodes + 1)

    def calculate_proofsize(self, succes_node):  #todo(sjh): make it compatible with this
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
        else:  # else it exists so append without writing the header
            pd.DataFrame(proofsize_records).to_csv(fname, mode='a', header=False, index=None)

        fname = f'{self.proofstep_path}{multiprocessing.current_process().name}_proofstep.csv'
        if not os.path.isfile(fname):
            pd.DataFrame(proofstep_records).to_csv(fname, header='column_names', index=None)
        else:  # else it exists so append without writing the header
            pd.DataFrame(proofstep_records).to_csv(fname, mode='a', header=False, index=None)

    def search(self):
        if not self.search_id is None:
            return self.__search()
        return 'Init search failed'

if __name__ == "__main__":
    class DemoGenerator:
        def __init__(self):
            self.random_list = [(0.3, "intros"),
                                (0.25, "have h:1=1"),
                                (0.2, "cases b"),
                                (0.15, "exfalso"),
                                (0.1, "simp")]

        def generate(self, text, e):
            return self.random_list[:e]

    server = LeanServer()
    generator = DemoGenerator()
    searcher = ProofHyperTreeSearch(server, generator, 5, 128, "cond_a_a", use_hyper_tree=False)
    print(searcher.search())