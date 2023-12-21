import json
import random
import os

def read_data(file_path, is_train):
    dir_list = os.listdir(file_path)
    print("dir_list:{}".format(dir_list))
    prove_tactic_temp = []
    decl2data = dict()
    decl2conditions = dict()
    init_state2decl = dict()
    init_states = []
    decl_name = None

    decl2lemma_line = dict()
    file_list = ["Trigo_0.lean", "Trigo_1.lean", "Trigo_2.lean", "Trigo_3.lean", "Trigo_4.lean", "Trigo_5.lean", "Trigo_6.lean", "Trigo_7.lean", "Trigo_8.lean"]
    for file_name in dir_list:
        #print("file_namee[-6:]:{}".format(file_name[-6:]))
        if file_name in file_list:#!= "all_trigo.lean" and file_name != "trigo_import.lean" and file_name != "unlabel_test.lean"  and ("emerge" in file_name) and ("olean" not in file_name) :
        #    print("file_name:{}".format(file_name))
        #    print("is_train:{}".format( is_train))
           if ("test" in file_name and is_train==True) or  ("emerge_step" in file_name and is_train==False) :
              continue
          
           
              
        
           final_file_name = file_path + "/" + file_name
           print("final_file_name:{}".format(final_file_name))
           with open (file = final_file_name, mode = "r", encoding = "utf-8") as file:
               data = file.read()
               for line in data.split("\n"):
                    if line == "import trigo_import" or line == "open real" or line == "open_locale real" or line == "variables (x y : ℝ)":
                       continue
                    
                    if "lemma" in line:
                        print("line:{}".format(line))
                        init_prove_state = line.split("lemma ")[1]
                        init_prove_states = init_prove_state.split(": ")
                        if "(" in init_prove_states[0]:
                             decl_name = init_prove_states[0].split(" (")[0]
                             
                             init_prove_state = (init_prove_state.split(":="))[0]
                             conditions = (((init_prove_state.split(") :"))[0]).split(decl_name))[1]
                             print("conditions:{}".format(conditions))
                             conditions = conditions + ")"
                             decl2conditions[decl_name.strip()] = conditions
                        else:
                             decl_name = init_prove_states[0]
                             decl2conditions[decl_name.strip()] = None
                    
                        
                        init_state = init_prove_states[-1].split(":=")[0]
                        init_state2decl[init_state] = decl_name 
                        #print("init_state:{}".format(init_state))
                        init_states.append(init_state)
                        prove_tactic_temp = []
                        decl2lemma_line[decl_name] =  line

                    elif "begin" in line or line == "":
                        continue 
                    elif "end" in line:
                        decl2data[decl_name.strip()] = prove_tactic_temp
                    else:
                        prove_tactic_temp.append(line.strip())
   # assert 1==0
    return decl2data, init_states, init_state2decl, decl2lemma_line, decl2conditions


decl2data, _, _, _,  decl2conditions= read_data("../../../lean_gym_tidy"+"/_target/deps/trigo/src", True)
print("decl2data.keys:{}".format(decl2data.keys()))




train_names_path = "train_raw_299_names.json"
with open(train_names_path) as f:
        train_names = json.load(f)
valid_names_path = "valid_raw_42_names.json"
with open(valid_names_path) as f:
        valid_names = json.load(f)






train_datas_temp = []
train_datas_temp.append("import trigo_import")
train_datas_temp.append("open real")
train_datas_temp.append("open_locale real")
train_datas_temp.append("variables (x y : ℝ)")
train_datas_temp.append("\n")


valid_datas_temp = []
valid_datas_temp.append("import trigo_import")
valid_datas_temp.append("open real")
valid_datas_temp.append("open_locale real")
valid_datas_temp.append("variables (x y : ℝ)")
valid_datas_temp.append("\n")

dir_list = os.listdir("./")

train_name_count= 0
valid_name_count= 0
name_count= 0
init_state_set = set()
for file_path in dir_list:
    if "from_raw_expand_step3_from_" not in file_path or ".json" not in file_path: #!="from_rule_data_step3_number_generalization.json":#if "bad_data" in file_path or "test_data" in file_path or ".py" in file_path or ".lean" in file_path:
        continue
    print("file_path:{}".format(file_path))
    with open(file_path) as f:
        train_datas = json.load(f)
    
    for i, data in enumerate(train_datas):
        #print("data:{}".format(data))
        decl = (data['decl_name']).strip()              # Trigo_2_233_EOKP Trigo_2_217_NWBU


        if decl == "Trigo_2_233_EOKP" or  decl == "Trigo_2_217_NWBU":
           continue

        print("decl:{}".format(decl))
        real_data = decl2data[decl.strip()]
        real_data_first = real_data[0]
        #print("real_data:{}".format(real_data))
        problem_conditions = data['problem_conditions']
        init_state = data["last_state"]
        prove_num = data["prove_step_num"]

        if init_state not in init_state_set:
           init_state_set.add(init_state)
        else:
           continue

        if prove_num !=3:
           continue

        decl_name = "lemma " + "Trigo" + "_" + "expand_step3_from_raw"+"_"+str(name_count) #+" : "
        conditions = decl2conditions[decl.strip()]
        if conditions != None:
           count = conditions.count(":")
           decl_name += " " + conditions
        else:
           count = 0

        
        if problem_conditions != None:
            
            for condition in problem_conditions:
                condition = condition.replace("--", "- -").replace("^", "**").replace("/-", "/ -")
                if (condition != "+") and (condition != "_") and (condition != ")") and (condition != "-"):
                    #print("===================================================================================================")
                    decl_name += " (" + "h"+ str(count) + " : " + condition + "≠ 0"+")"
                    #print("decl_name:{}".format(decl_name))
                    count += 1


        decl_name = decl_name + " : " + init_state.replace("--", "- -").replace("^", "**").replace("/-", "/ -") + ":="
        tactics_temp = []
        flag = False

        for tactic in data["proves_tactics"]:
             if tactic ==real_data_first:
                flag = True
                break
        
        if flag == False:
        #    print("real_data:{}".format(real_data))
        #    print("data[proves_tactics]:{}".format(data["proves_tactics"]))
           assert 1==0

        for tactic in data["proves_tactics"]:
           
               
            tactic = tactic.replace("--", "- -").replace("\n","").replace("      "," ").replace("      "," ").replace("    "," ").replace("   "," ").replace("  "," ").replace("^", "**").replace("/-", "/ -")
            tactics_temp.append(tactic)

        data = ("\n".join(tactics_temp)).replace("--", "- -").replace("^", "**").replace("/-", "/ -").replace("sin ", "sin").replace("cos ", "cos").replace("tan ", "tan").replace("cospi", "cos(pi)").replace("sinpi", "sin(pi)").replace("sin0", "sin(0)").replace("cos0", "cos(0)").replace("tanpi", "tan(pi)").replace("tan0", "tan(0)").replace("sinx", "sin(x)").replace("cosx", "cos(x)").replace("tanx", "tan(x)").replace("sin8", "sin(8)").replace("cos8", "cos(8)").replace("sin16", "sin(16)").replace("sin1", "sin(1)").replace("cos1", "cos(1)").replace("sin4", "sin(4)").replace("cos4", "cos(4)").replace("sin2", "sin(2)").replace("cos2", "cos(2)").replace("siny", "sin(y)").replace("cosy", "cos(y)").replace("tany", "tan(y)").replace("sin3", "sin(3)").replace("cos3", "cos(3)")#data.replace("\n", " ")
      
        if decl in train_names:
            
            if train_name_count >= 10100:
               continue
            train_name_count = train_name_count + 1 
            train_datas_temp.append(decl_name)
            train_datas_temp.append("begin")
            train_datas_temp.append(data)
            train_datas_temp.append("end")
            train_datas_temp.append("\n")
            

            
        else:
            
            if valid_name_count >= 1100:
               continue  
            valid_name_count = valid_name_count + 1 
            valid_datas_temp.append(decl_name)
            valid_datas_temp.append("begin")
            valid_datas_temp.append(data)
            valid_datas_temp.append("end")
            valid_datas_temp.append("\n")
            
   
            
        
        name_count += 1 



train_datas_str = "\n".join(train_datas_temp)

all_data_strs = train_datas_str#strs + train_datas_str
with open("train_raw_expand_step3_10000.lean","w") as file:
    file.write(all_data_strs)



valid_datas_str = "\n".join(valid_datas_temp)

all_data_strs = valid_datas_str#strs + train_datas_str
with open("valid_raw_expand_step3_1000.lean","w") as file:
    file.write(all_data_strs)