import json
import random
import os


train_datas_temp = []
train_datas_temp.append("import trigo_import")
train_datas_temp.append("open real")
train_datas_temp.append("open_locale real")
train_datas_temp.append("variables (x y : ℝ)")
train_datas_temp.append("\n")

dir_list = os.listdir("./")

name_count= 0
init_state_set = set()
for file_path in dir_list:
    # if "bad_data" in file_path or "test_data" in file_path or ".py" in file_path or ".lean" in file_path:
    #     continue
    if file_path !="from_rule_data_step1_number_generalization_2.json":
       continue
    print("file_path:{}".format(file_path))
    with open(file_path) as f:
        train_datas = json.load(f)
    
    for i, data in enumerate(train_datas):
        #print("data:{}".format(data))
        problem_conditions = data['problem_conditions']
        init_state = data["last_state"]
        prove_num = data["prove_step_num"]

        if init_state not in init_state_set:
           init_state_set.add(init_state)
        else:
           continue
        
        print("")
        if prove_num !=1:
           continue

        decl_name = "lemma " + "Trigo" + "_" + str(name_count) #+" : "
        count = 0
        if problem_conditions != None:
            
            for condition in problem_conditions:
                condition = condition.replace("--", "- -").replace("^", "**").replace("/-", "/ -")
                if (condition != "+") and (condition != "_") and (condition != ")") and (condition != "-"):
                    print("===================================================================================================")
                    decl_name += " (" + "h"+ str(count) + " : " + condition + "≠ 0"+")"
                    print("decl_name:{}".format(decl_name))
                    count += 1


        decl_name = decl_name + " : " + init_state.replace("--", "- -").replace("^", "**").replace("/-", "/ -") + ":="
        tactics_temp = []
        for tactic in data["proves_tactics"]:
            tactic = tactic.replace("--", "- -").replace("\n","").replace("      "," ").replace("      "," ").replace("    "," ").replace("   "," ").replace("  "," ").replace("^", "**").replace("^", "**").replace("/-", "/ -")
            tactics_temp.append(tactic)

        data = ("\n".join(tactics_temp)).replace("--", "- -").replace("^", "**").replace("/-", "/ -").replace("sin ", "sin").replace("cos ", "cos").replace("tan ", "tan").replace("cospi", "cos(pi)").replace("sinpi", "sin(pi)").replace("sin0", "sin(0)").replace("cos0", "cos(0)").replace("tanpi", "tan(pi)").replace("tan0", "tan(0)")
        train_datas_temp.append(decl_name)
        train_datas_temp.append("begin")
        train_datas_temp.append(data)
        train_datas_temp.append("end")
        train_datas_temp.append("\n")
        name_count = name_count + 1 
        print("name_count:{}".format(name_count))
        if name_count == 1002:
            break

    if name_count == 1002:
            break


train_datas_str = "\n".join(train_datas_temp)

all_data_strs = train_datas_str#strs + train_datas_str
with open("from_rule_data_emerge_number_generalization_step1_2.lean","w") as file:
    file.write(all_data_strs)