import subprocess
import os

LEAN_PATH = os.path.expanduser('~/.elan/bin/lean')
LEAN_GYM_DIR = os.path.join(os.path.dirname(os.path.realpath(__file__)), 
            'lean_gym')

class LeanFatalError(Exception):
    """Raise when Lean fatal error ocurred"""
    pass

class LeanServer:

    def __init__(self,
                 lean_path=LEAN_PATH,
                 lean_gym_dir=LEAN_GYM_DIR,
                 normalize_tab=True,
                 ):
        self.proc = subprocess.Popen([lean_path, '--run', 'src/repl.lean'],
                                     stdin=subprocess.PIPE,
                                     stdout=subprocess.PIPE,
                                     stderr=subprocess.PIPE,
                                     cwd=lean_gym_dir)
        self.is_alive = True
        self.has_init = False
        self.normalize_tab = normalize_tab

    def init_search(self, dec_name, namespaces=""):
        inputs = f'["init_search", ["{dec_name}","{namespaces}"]]\n'
        return self.__run(inputs)
    
    def run_tac(self, search_id, tactic_id, tactic):
        import re
        tactic = "".join(re.findall("[^\n\t\a\b\r]+",tactic))
        inputs = f'["run_tac", ["{search_id}", "{tactic_id}", "{tactic}"]]\n'
        return self.__run(inputs)
    
    def clear_search(self, search_id):
        inputs = f'["clear_search",["{search_id}"]]\n'
        return self.__run(inputs)
    
    def __output_parse(self, output):
        null = None
        # TODO: varify if output is empty is definitly fatal error
        if len(output) <= 0:
            raise LeanFatalError
        output = eval(output)
        if output['search_id'] is not None:
            output['search_id'] = int(output['search_id'])
        if output['tactic_state_id'] is not None:
            output['tactic_state_id'] = int(output['tactic_state_id'])
        if self.normalize_tab:
            if output['tactic_state'] is not None:
                # assert not '\t' in output['tactic_state']
                output['tactic_state'] = output['tactic_state'].replace(
                    '\t', ' ')
        return output

    def __run(self, inputs):
        if not self.is_alive:
            return {'error':'proc_killed','search_id':None, 'tactic_state':None, 'tactic_state_id':None}
        self.proc.stdin.write(inputs.encode())
        self.proc.stdin.flush()
        return self.__output_parse(self.proc.stdout.readline().decode())
    
    def kill(self):
        self.is_alive = False
        self.proc.kill()

        
if __name__=='__main__':
    
    server = LeanServer()#LeanServer(lean_gym_dir="/home/ma-user/work/xiongjing/hwatp_autogenerate/lean_gym")

    while 1:
        tactic = input("input tactic:")
        if tactic == "init":
            decl_name = input("decl name:")
            name_space = input("name space:")
            output = server.init_search(decl_name, name_space)
            search_id = output["search_id"]
            print(output)
        elif tactic == "exit":
            break
        else:
            tactic_id = None
            while tactic_id is None:
                try:
                    tactic_id = int(input("tactic id:"))
                except:
                    tactic_id = None
            output = server.run_tac(search_id, tactic_id, tactic)
            print(output)
    

