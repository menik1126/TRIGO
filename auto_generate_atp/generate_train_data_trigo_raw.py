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
file_name_list = ["Trigo_0.lean", "Trigo_1.lean", "Trigo_2.lean", "Trigo_3.lean", "Trigo_4.lean", "Trigo_5.lean", "Trigo_6.lean", "Trigo_7.lean", "Trigo_8.lean"]
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
        if file_name in file_name_list :
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
from lean_server_tidy import *
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
     
    with open (file = "generated_data/trigo_data/test_valid_names_set.txt", mode = "r", encoding = "utf-8") as file:
               data_names = file.read()
    data_names = data_names.split("\n")
    test_names = []
    for data in data_names:
        name = (data.split(" "))[0]
        test_names.append(name.strip())

    decl2data, init_states, init_state2decl, decl2lemma_line = read_data("../lean_gym_tidy"+"/_target/deps/trigo/src", is_train)
    all_prove_texts = []
    all_prove_texts_valid = []
    print("keys:{}".format(decl2data.keys()))
    if is_train == True:
       decl2data_list = (list(decl2data.keys()))#[start_index:start_index+1000]
    
    train_and_valid_names = []
    for decl in decl2data_list:
        if decl.strip() not in test_names:
           train_and_valid_names.append(decl.strip())
    random.shuffle(train_and_valid_names)
    
    print("len of train_and_valid_names:{}".format(len(train_and_valid_names)))
    train_names = train_and_valid_names[:299]
    valid_names = train_and_valid_names[299:]
    print("len of train:{}".format(len(set(train_names))))
    print("len of valid:{}".format(len(set(valid_names))))
    index_count = 0
    all_train_datas = []
    all_valid_datas = []
    all_timeout_decl = []

    time_outs = ["Trigo_0_129_COJG", "Trigo_0_142_NHYP ", "Trigo_0_143_RDGT", "Trigo_1_151_EOYC", "Trigo_1_158_WJWZ", "Trigo_1_164_HNWO", "Trigo_1_173_HJXB ", "Trigo_1_174_XOWB", "Trigo_1_179_LPWJ", "Trigo_1_180_DFLS", "Trigo_1_187_TXAZ ", "Trigo_1_189_KEAM ", "Trigo_1_196_IFKW ", "Trigo_2_203_KQQP", "Trigo_2_215_CBML ", "Trigo_2_218_JEUS", "Trigo_2_222_ZDRD ", "Trigo_2_234_GIRS", "Trigo_2_235_PZHG ", "Trigo_2_236_IXFH", "Trigo_2_243_PTCJ", "Trigo_2_249_YOAQ", "Trigo_3_299_ROBF ", "Trigo_4_300_HVNS", "Trigo_4_304_VPTQ", "Trigo_4_309_BJMY", "Trigo_4_315_JZKD", "Trigo_4_320_QBWT ", "Trigo_4_326_TRVW", "Trigo_4_327_DOGX", "Trigo_4_329_APFG ", "Trigo_4_330_QHIH", "Trigo_4_333_RAEI", "Trigo_4_337_VMBT", "Trigo_4_344_QPKD", "Trigo_4_348_WZTA", "Trigo_5_355_QVHL", "Trigo_5_357_SLFQ", "Trigo_5_360_XQHO", "Trigo_5_361_KOPV", "Trigo_5_363_KGWA", "Trigo_5_369_EPCK", "Trigo_5_371_UQCA", "Trigo_5_375_EZCK", "Trigo_5_385_SWHN", "Trigo_5_390_CVUX", "Trigo_5_391_NULQ", "Trigo_5_395_KSOQ", "Trigo_5_396_SLLC ", "Trigo_5_397_YLLO", "Trigo_6_403_YJZW ", "Trigo_6_405_KQQA", "Trigo_6_410_RSSE", "Trigo_6_411_BEZS", "Trigo_6_412_HKDG", "Trigo_6_413_QUEC", "Trigo_6_414_SIUE", "Trigo_6_416_ZILP", "Trigo_6_417_SNCF", "Trigo_6_419_RVIC", "Trigo_6_420_EELP", "Trigo_6_422_EEVG "]
    
    for decl in tqdm(decl2data_list):
        
        if decl.strip() not in test_names:#"Trigo_3_261_OXAZ_extend(h0":
           continue
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
        
        flag = False
        for tactic in all_tactics_old:
            if tactic == "{" or tactic == "},":
                all_tactics.append(tactic)
                continue
            tactic = tactic.replace("π", "pi")
            print("tactic:{}".format(tactic))
            print("search_id:{}".format(search_id))
            print("tactic_state_id:{}".format(tactic_state_id))
            lean_output = leanserver.run_tac(search_id, tactic_state_id, tactic)
            print("lean_output:{}".format(lean_output))
          
            search_id = lean_output['search_id']
            tactic_state_id = lean_output['tactic_state_id']
            error = lean_output['error']
            print("=====================================================start0")
            print("last_tactic_state:{}".format(last_tactic_state))
            print("tactic:{}".format(tactic))
            print("=======================================================end0")
            if error != None:
               all_timeout_decl.append(decl)
               flag = True
               #assert error == None
               break
               
            all_tactics.append(tactic)
            train_line = "DECL " + decl.strip() + " GOAL " + last_tactic_state + " PROOFSTEP " + tactic
            train_data_dict = dict()
            print("=====================================================start1")
            print("last_tactic_state:{}".format(last_tactic_state))
            print("tactic:{}".format(tactic))
            print("=======================================================end1")
            train_data_dict["GOAL"] = last_tactic_state
            train_data_dict["PROOFSTEP"] = tactic
            train_data_dict["DECL"] = decl.strip()

            last_tactic_state = lean_output['tactic_state']
            

            # if decl.strip() in train_names:
            #    all_train_datas.append(train_data_dict)
            # elif decl.strip() in valid_names:
            #    all_valid_datas.append(train_data_dict)
              
            all_train_datas.append(train_data_dict)
        
        if flag==True:
           continue

        print("end of lean_output:{}".format(lean_output))
        tactic_state = lean_output['tactic_state']
        assert tactic_state == "no goals"
        leanserver.clear_search(search_id)

        lemma_line = decl2lemma_line[decl]
        prove_process = "\n".join(all_tactics)
        

        all_prove_text = lemma_line + "\n" + "begin" + "\n" + prove_process + "\n" + "end" + "\n"


       
        index_count += 1

    print("index_count:{}".format(index_count))
    print("len:{}".format(len(test_names)))
    if is_train == True:
        with open("generated_data/" + "trigo_data" + "/test_raw_new" + ".json","w") as file:
            json.dump(all_train_datas ,file)
        # with open("generated_data/" + "trigo_data" + "/valid_raw_42_new" + ".json","w") as file:
        #     #file.write(all_train_datas)
        #     #random.shuffle(all_valid_datas)
        #     json.dump(all_valid_datas ,file)

        # with open("generated_data/" + "trigo_data" + "/train_raw_299_names" + ".json","w") as file:
        #     #file.write(all_train_datas)
        #     #random.shuffle(all_train_datas)
        #     json.dump(train_names, file)
        # with open("generated_data/" + "trigo_data" + "/valid_raw_42_names" + ".json","w") as file:
        #     #file.write(all_train_datas)
        #     #random.shuffle(all_valid_datas)
        #     json.dump(valid_names, file)
        
        # with open("generated_data/" + "trigo_data" + "/raw_299_tidy" +"_" + "timeout" + ".json","w") as file:
        #     #file.write(all_train_datas)
        #     json.dump(all_timeout_decl ,file)