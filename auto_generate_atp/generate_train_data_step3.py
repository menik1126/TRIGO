from sympy import *
import random
from rule_matcher import *
from naive_replace import *
from utils_trigo import get_denominators
import re

common_calc_steps = [
    'focus{repeat {apply congr_arg _}}',
    'try {simp}',
    'ring'
]


const_list = [2*pi, pi, pi/2, pi/3, pi/6, -pi/6, -pi/3, -pi/2, -pi, -2*pi]
import os
def read_data(file_path, is_train):
    dir_list = os.listdir(file_path)
    print("dir_list:{}".format(dir_list))
    prove_tactic_temp = []
    decl2data = dict()
    init_state2decl = dict()
    init_states = []
    decl_name = None

    decl2lemma_line = dict()
    for file_name in dir_list:
        if file_name != "all_trigo.lean" and file_name != "trigo_import.lean" and file_name != "unlabel_test.lean"  and ("after" in file_name) and ("olean" not in file_name) :
           if ("test" in file_name and is_train==True) or  ("rule_data" in file_name and is_train==False) :
              continue
           final_file_name = file_path + "/" + file_name
           print("final_file_name:{}".format(final_file_name))
           with open (file = final_file_name, mode = "r", encoding = "utf-8") as file:
               data = file.read()
               for line in data.split("\n"):
                    if line == "import trigo_import" or line == "open real" or line == "open_locale real" or line == "variables (x y : ℝ)":
                       continue
                    
                    if "lemma" in line:
                        init_prove_state = line.split("lemma ")[1]
                        init_prove_states = init_prove_state.split(": ")
                        if "(" in init_prove_states[0]:
                             decl_name = init_prove_states[0].split(" (")[0]
                        else:
                             decl_name = init_prove_states[0]
                    
                        
                        init_state = init_prove_states[-1].split(":=")[0]
                        init_state2decl[init_state] = decl_name 
                        init_states.append(init_state)
                        prove_tactic_temp = []
                        decl2lemma_line[decl_name] =  line

                    elif "begin" in line or line == "":
                        continue 
                    elif "end" in line:
                        decl2data[decl_name] = prove_tactic_temp
                    else:
                        prove_tactic_temp.append(line.strip())

    return decl2data, init_states, init_state2decl, decl2lemma_line

import json 
from lean_server_step3 import *
import copy
import random
from tqdm import tqdm
import argparse

if __name__ == "__main__":
    bracket_list=["sin(X)*sin(Y)=cos(X - Y)/2 - cos(X + Y)/2", "sin(X)*cos(Y)=sin(X - Y)/2 + sin(X + Y)/2", "cos(X)*cos(Y)=cos(X - Y)/2 + cos(X + Y)/2", "sin(Y)*cos(X)=-sin(X - Y)/2 + sin(X + Y)/2", "tan(X)*tan(Y)=(tan(X) - tan(Y))/tan(X - Y) - 1", "tan(X)*tan(Y)=-(tan(X) + tan(Y))/tan(X + Y) + 1",
                  "sin(X) + sin(Y)=2*sin(X/2 + Y/2)*cos(X/2 - Y/2)", "sin(X) - sin(Y)=2*sin(X/2 - Y/2)*cos(X/2 + Y/2)", "cos(X) + cos(Y)=2*cos(X/2 - Y/2)*cos(X/2 + Y/2)", "cos(X) - cos(Y)=-2*sin(X/2 - Y/2)*sin(X/2 + Y/2)", "tan(X) + tan(Y)=(-tan(X)*tan(Y) + 1)*tan(X + Y)", "tan(X) - tan(Y)=(tan(X)*tan(Y) + 1)*tan(X - Y)", "tan(X) - tan(Y)=sin(X - Y)/(cos(X)*cos(Y))"   ,  
                  "sin(X)/cos(X)=tan(X)"]
    
    bad_init_axiom = ['tan(2*X)=2*tan(X)/(1 - tan(X)**2)', 'tan(X/2)=(1 - cos(X))/sin(X)', 'tan(X/2)=sin(X)/(1+ cos(X))', 'tan(X - Y)=(tan(X) - tan(Y))/(1 + tan(X)*tan(Y))', 'Abs(X)=X', 'tan(X) + tan(Y)=(-tan(X)*tan(Y) + 1)*tan(X + Y)', 'tan(X) - tan(Y)=(tan(X)*tan(Y) + 1)*tan(X - Y)', 'tan(X) - tan(Y)=sin(X - Y)/(cos(X)*cos(Y))', 'tan(X)*tan(Y)=(tan(X) - tan(Y))/tan(X - Y) - 1', 'tan(X)*tan(Y)=-(tan(X) + tan(Y))/tan(X + Y) + 1']
    decl2generated_tactics = dict()
    decl2generated_states = dict()
    decl2generated_all_tactics = dict()
    leanserver = LeanServer()
    
    

    parser = argparse.ArgumentParser()
    parser.add_argument('--start_index', type=int, default=1000)
    parser.add_argument('--step_count', type=int, default=3)
    parser.add_argument('--is_train', type=bool, default=False)
    args = parser.parse_args()
    start_index = args.start_index
    step_count = args.step_count
    is_train = args.is_train

    decl2data, init_states, init_state2decl, decl2lemma_line = read_data("../lean_gym_step"+str(step_count)+"/_target/deps/trigo/src", is_train)
    all_prove_texts = []
    print("type of key:{}".format(type(decl2data.keys())))
    if is_train == True:
       decl2data_list = (list(decl2data.keys()))[start_index:start_index+1000]
    else:
       decl2data_list = (list(decl2data.keys()))
 
    index_count = 0
    all_train_datas = []
    for decl in tqdm(decl2data_list):
        print("===============decl:{}".format(decl))
        all_tactics_old = decl2data[decl]
        lean_output = leanserver.init_search(decl.strip(), "real")
        print("init of lean_output:{}".format(lean_output))
        search_id = lean_output['search_id']
        tactic_state_id = lean_output['tactic_state_id']
        
        lean_output = leanserver.run_tac(search_id, tactic_state_id, "intros")
        search_id = lean_output['search_id']
        tactic_state_id = lean_output['tactic_state_id']
        last_tactic_state = lean_output["tactic_state"]
        print("start of lean_output:{}".format(lean_output))
        all_tactics = []
        

        for tactic in all_tactics_old:
            if tactic == "{" or tactic == "},":
                all_tactics.append(tactic)
                continue
            print("tactic:{}".format(tactic))
            print("search_id:{}".format(search_id))
            print("tactic_state_id:{}".format(tactic_state_id))
            lean_output = leanserver.run_tac(search_id, tactic_state_id, tactic)
            print("lean_output:{}".format(lean_output))
          
            search_id = lean_output['search_id']
            tactic_state_id = lean_output['tactic_state_id']
            error = lean_output['error']
            assert error == None
            all_tactics.append(tactic)
            train_line = "GOAL " + last_tactic_state + " PROOFSTEP " + tactic
            train_data_dict = dict()
            train_data_dict["GOAL"] = last_tactic_state
            train_data_dict["PROOFSTEP"] = tactic
            train_data_dict["DECL"] = decl.strip()
            last_tactic_state = lean_output['tactic_state']
            

            all_train_datas.append(train_data_dict)#train_line)

        print("end of lean_output:{}".format(lean_output))
        tactic_state = lean_output['tactic_state']
        assert tactic_state == "no goals"
        leanserver.clear_search(search_id)

        lemma_line = decl2lemma_line[decl]
        prove_process = "\n".join(all_tactics)
        

        all_prove_text = lemma_line + "\n" + "begin" + "\n" + prove_process + "\n" + "end" + "\n"
        all_prove_texts.append(all_prove_text)
        index_count += 1

    #all_train_datas_str = "\n".join(all_train_datas)
    if is_train == True:
        with open("generated_data/" + "train_txt_step" + str(step_count) + "/train_txt_step"+ str(step_count) +"_" + str(start_index) + ".json","w") as file:
            #file.write(all_train_datas)
            json.dump(all_train_datas ,file)
    else:
        with open("generated_data/" + "train_txt_step" + str(step_count) + "/train_txt_step"+ str(step_count) +"_" + "test" + ".json","w") as file:
            #file.write(all_train_datas)
            json.dump(all_train_datas ,file)