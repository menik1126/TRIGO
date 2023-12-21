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


    
# axiom.rule:sin(X)*cos(Y)=sin(X - Y)/2 + sin(X + Y)/2
# {X + Y: 0, X - Y: pi/2}

# axiom.rule:sin(X) + sin(Y)=2*sin(X/2 + Y/2)*cos(X/2 - Y/2)
# state:sin(pi/4 - pi/4)/2 + sin(pi/4 + pi/4)/2=1/2




const_list = [2*pi, pi, pi/2, pi/3, pi/6, -pi/6, -pi/3, -pi/2, -pi, -2*pi]
def init_state_function(axiom):
    name_space = "real"
    lean_output = leanserver.init_search("original_data", name_space)
    lean_output  = leanserver.run_tac(lean_output["search_id"], lean_output["tactic_state_id"], "intros")
    
    rule = axiom.rule
    has_nonzero = axiom.has_nonzero


    #print("rule:{}".format(rule))
    substitution = dict()
    left_expr, right_expr = rule.split("=")
    print("left_expr:{}".format(left_expr))
    print("right_expr:{}".format(right_expr))
    if "X" in rule:
       value_X = random.choice(const_list) 
       substitution[sympify("X")] = sympify(str(value_X))

    if "Y" in rule:
       value_Y = None
       for i in  range(1000):
           value_Y = random.choice(const_list)
           if str(value_Y) != str(value_X):
              break 
       substitution[sympify("Y")] = sympify(str(value_Y))


    if "K" in rule:
       value_K = str(random.randint(0,100))
       substitution[sympify("K")] = sympify(str(value_K))

    substitution_left_expr, substitution = parse_and_replace(left_expr, substitution)
    substitution_right_expr, substitution = parse_and_replace(right_expr, substitution)

    substitution_left_expr = (" ".join(substitution_left_expr)).replace("0 -","-")
    substitution_right_expr = (" ".join(substitution_right_expr)).replace("0 -","-")
    print("substitution_left_expr:{}".format(substitution_left_expr))
    print("substitution_right_expr:{}".format(substitution_right_expr))


    new_state = substitution_left_expr + "=" + substitution_right_expr
    problem_conditions_all = []
    if has_nonzero:
        non_zeros = axiom.get_nonzero(substitution, None, None) 
        for non_zero in non_zeros:
            problem_conditions_all.append(non_zero)

    init_axiom_tactics = axiom.get_tactics(substitution, substitution_left_expr, substitution_right_expr)
    init_axiom_tactics =  ["have : "+ substitution_left_expr + "  =  " + substitution_right_expr +","] + ["{"] + init_axiom_tactics + ["},"] + ["rw this,"]
    tactics_forward = ["have : "+ substitution_left_expr + "  =  " + substitution_right_expr +","]  
    
    print("============================================================init_axiom_tactics:{}".format(init_axiom_tactics))
    _, excute_tactics, lean_output_ = excute_lean_gym(leanserver, init_axiom_tactics, lean_output)
    lean_output, _, _ = excute_lean_gym(leanserver, tactics_forward, lean_output)  #excute_lean_gym(tactics)
    
    
    print("============================================================init excute_tactics:{}".format(excute_tactics))
    print("============================================================init lean_output_:{}".format(lean_output_))
    # 在这里传入i
    tactics_prove = get_prove_tactic_init(axiom.rule, excute_tactics, substitution_left_expr, substitution_right_expr)

    # print("init lean_output:{}".format(lean_output))
    # print("new_state:{}".format(new_state))
    # print("substitution:{}".format(substitution))
    return  lean_output,  tactics_prove, new_state, problem_conditions_all#lean_output,  init_axiom_tactics, new_state, problem_conditions_all



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
        #print("file_namee[-6:]:{}".format(file_name[-6:]))
        if file_name == "valid_raw_expand_step3_1000.lean":#"train_raw_expand_step3_10000.lean":#
           print("file_name:{}".format(file_name))
           print("is_train:{}".format( is_train))


           final_file_name = file_path + "/" + file_name
           print("final_file_name:{}".format(final_file_name))
           with open (file = final_file_name, mode = "r", encoding = "utf-8") as file:
               data = file.read()
               #print("data:{}".format(data))
               for line in data.split("\n"):
                    if line == "import trigo_import" or line == "open real" or line == "open_locale real" or line == "variables (x y : ℝ)":
                       continue
                    
                    if "lemma" in line:
                        #print("line:{}".format(line))
                        init_prove_state = line.split("lemma ")[1]
                        init_prove_states = init_prove_state.split(": ")
                        if "(" in init_prove_states[0]:
                             decl_name = init_prove_states[0].split(" (")[0]
                             #print("decl_name:{}".format(decl_name))
                        else:
                             decl_name = init_prove_states[0]
                    
                        
                        init_state = init_prove_states[-1].split(":=")[0]
                        init_state2decl[init_state] = decl_name 
                        #print("init_state:{}".format(init_state))
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
from lean_server import *
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
    parser.add_argument('--start_index', type=int, default=0)
    parser.add_argument('--step_count', type=int, default=3)
    parser.add_argument('--is_train', type=bool, default=True)
    args = parser.parse_args()
    start_index = args.start_index
    step_count = args.step_count
    is_train = args.is_train

    decl2data, init_states, init_state2decl, decl2lemma_line = read_data("../lean_gym"+"/_target/deps/trigo/src", is_train)
    all_prove_texts = []
    print("type of key:{}".format(type(decl2data.keys())))
    #decl2data_list = (list(decl2data.keys()))[:1000]
    #decl2data_list = list(decl2data.keys())
    print("decl2data_list:{}".format(len(list(decl2data.keys()))))
    decl2data_list = (list(decl2data.keys()))[start_index:]#start_index+2000]#[start_index:]#[start_index:start_index+2000]
    index_count = 0
    
    all_timeout_decl = []
    for decl in tqdm(decl2data_list):
        #print("===============decl:{}".format(decl))
        # if decl.strip() != "Trigo_2_218_JEUS_extend(h0":   # Trigo_2_218_JEUS_extend Trigo_5_368_BLFE_extend
        #    continue
        
        all_tactics_old = decl2data[decl]
        
        lemma_line = (decl2lemma_line[decl]).replace("_expand", "_step3_valid")

        #print("lemma_line:{}".format(lemma_line))
        lean_output = leanserver.init_search(decl, "real")
        search_id = lean_output['search_id']
        tactic_state_id = lean_output['tactic_state_id']
        
        lean_output = leanserver.run_tac(search_id, tactic_state_id, "intros")
        search_id = lean_output['search_id']
       
        tactic_state_id = lean_output['tactic_state_id']
        last_tactic_state = lean_output["tactic_state"]
        
        all_tactics = []
        count = 0
        flag = False
        #print("all_tactics_old:{}".format(all_tactics_old))
        for tactic in all_tactics_old:
            tactic = tactic.replace("π", "pi")
            #print("000tactic:{}".format(tactic))
            if count !=0:
               # 在这里跳过所有相等的数据
               count = count -1
               #print("skip=========")
               continue

            if tactic == "{" or tactic == "},":
                #all_tactics.append(tactic)
                continue
            # print("tactic:{}".format(tactic))
            # print("search_id:{}".format(search_id))
            #print("0here====================")
            lean_output = leanserver.run_tac(search_id, tactic_state_id, tactic)
            #print("lean_output:{}".format(lean_output))
            if "have" in tactic:
               equality = (tactic.split(" :"))[1]
               if "=" in equality: 
                    left = ((equality.split("="))[0]).strip()
                    right = ((equality.split("="))[1]).strip()
               else:
                    left = ((equality.split("≠"))[0]).strip()
                    right = ((equality.split("≠"))[1]).strip()
                    
               left = left.replace(" ","").replace("^","**").replace("\n","").replace(",","")
               right = right.replace(" ","").replace("^","**").replace("\n","").replace(",","")
               
               if left == right:
                  count = 4   
                  #print("have here=====================")
                  continue
            #print("1here====================")
            # 去掉前后状态相等的tactic
            error = lean_output['error']
            if error != None:
            #    print("")
            #    print("lean_output:{}".format(lean_output))
            #    print("===============decl:{}".format(decl))
               all_timeout_decl.append(decl)
               flag = True
               #assert error == None
               break
            
            if  (lean_output['tactic_state']).replace(" ","").replace("\n","") == (last_tactic_state).replace(" ","").replace("\n",""):
                continue
            
            if "try" in tactic:
               tactic = tactic.replace("try {","").replace("},",",")
            
            #print("2here====================")
            last_tactic_state = lean_output['tactic_state']
            search_id = lean_output['search_id']
            tactic_state_id = lean_output['tactic_state_id']

            #print("111tactic:{}".format(tactic))
            all_tactics.append(tactic)
        #print("lean_output:{}".format(lean_output))
        if flag==True:
           continue
        
        tactic_state = lean_output['tactic_state']
        assert tactic_state == "no goals"
        leanserver.clear_search(search_id)


        prove_process = "\n".join(all_tactics)
        
        all_prove_text = lemma_line + "\n" + "begin" + "\n" + prove_process + "\n" + "end" + "\n"
        #print("all_prove_text:{}".format(all_prove_text))
        all_prove_texts.append(all_prove_text)
        index_count += 1

    all_prove_process = "\n\n".join(all_prove_texts)
    print("index_count:{}".format(index_count))
    with open("generated_data/" + "trigo_data" + "/trigo_expand_step3_valid_after_delete_1000" +"_"+str(start_index)+ ".lean","w") as file:
        file.write(all_prove_process)
    with open("generated_data/" + "trigo_data" + "/trigo_expand_step3_valid_after_delete_1000"+"_"+str(start_index) +"_" + "timeout" + ".json","w") as file:
        json.dump(all_timeout_decl ,file)
