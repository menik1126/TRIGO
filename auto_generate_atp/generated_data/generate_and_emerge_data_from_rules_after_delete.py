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

global_flag = False
pre_flag = False
for file_path in dir_list:
    if "bad_data" in file_path or "test" in file_path or ".py" in file_path or ".json" in file_path or ("after" not in file_path):
        continue
    

    print("file_path:{}".format(file_path))
    with open(file_path) as f:
        train_datas = (f.read()).split("\n")
    flag = False
    for i, line in enumerate(train_datas):
    

        line = line
        if line == "import trigo_import" or line == "open real" or line == "open_locale real" or line == "variables (x y : ℝ)":
            continue
        
        if "lemma" in line:
           print("line:{}".format(line))
           formula = (line.split(" : ")[-1]).split(":=")[0]
           print("formula:{}".format(formula))
           left = formula.split("=")[0]
           right = formula.split("=")[1]
           if left.replace(" ","") == right.replace(" ",""):
              flag = True
           else:
              name_count += 1
        
        if line.strip() == "end":
           if flag == True:
              pre_flag =True
           flag = False
           if name_count == 10000:
              global_flag = True
              break

    
        if flag == True or pre_flag == True:
            pre_flag = False
            continue

        train_datas_temp.append(line)
    
    if global_flag == True:
       train_datas_temp.append("end")
       break
    
    



print("name_count:{}".format(name_count))
train_datas_str = "\n".join(train_datas_temp)

all_data_strs = train_datas_str#strs + train_datas_str
with open("from_rule_data_step1_after_delete.lean","w") as file:
    file.write(all_data_strs)