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
all_train_datas = []
all_valid_datas = []
for file_path in dir_list:
    if  ".py" in file_path or ".txt" in file_path:
        continue
    print("file_path:{}".format(file_path))
    with open(file_path) as f:
        train_datas = json.load(f)

    
    for i, data in enumerate(train_datas):
        GOAL = data["GOAL"]
        PROOFSTEP = data["PROOFSTEP"]
        OLD_GOAL = GOAL 
      #   print("================================================================================================================================start")
      #   print("GOAL:\n{}".format(GOAL))
        GOAL_NUM = None
        if "goals" in GOAL:
           GOAL_NUM = GOAL.split("goals")[0] + "goals" + "\n"
           GOAL  = GOAL.split("goals")[1]
           
           #print("GOAL_NUM:{}".format(GOAL_NUM))
        
        #print("=========GOALS:\n{}".format(GOAL))
        
        GOAL_list = GOAL.split("\n\n")
        #print("GOAL_list:\n{}".format(GOAL_list))
        all_goals = []
        all_conditions = []
        all_last_this = []
        flag = False
        for GOAL in GOAL_list:
            #print("init_GOAL:\n{}".format(GOAL))
            #print("===========split0")
            this_list = GOAL.split("⊢")[0]
            goal = "⊢" + GOAL.split("⊢")[1]
            #print("0this_list:\n{}".format(this_list))
            this_list = this_list.split("this :")
            # print("1this_list:\n{}".format(this_list))
            # print("goal:\n{}".format(goal))
            condition = None
            for this in this_list:
                if ":" in this:
                    condition = this
                    flag = True
            
            if len(this_list) == 1:
               last_this = None
               flag = False
            else:
               last_this = this_list[-1]
            
            all_goals.append(goal)
            all_conditions.append(condition)
            all_last_this.append(last_this)
                   

      #   print("all_goals:{}".format(all_goals))
      #   print("all_conditions:{}".format(all_conditions))
      #   print("all_last_this:{}".format(all_last_this))
        if GOAL_NUM != None:
           new_state = GOAL_NUM
        else:
           new_state = ""

        for (goal, condition, last_this) in zip(all_goals, all_conditions, all_last_this):
            if condition != None:
               if condition[0]=="\n":
                  condition = condition[1:]
               #print("condition:{}".format(condition))
               new_state += condition
            
            if last_this != None:
               new_state += "this :" + last_this
            new_state += goal + "\n\n"
        
        
      #   print("=======GOAL:\n{}".format(OLD_GOAL))
      #   print("=======new_state:\n{}".format(new_state))

      #  print("================================================================================================================================end")
      #   if flag == True:
      #      assert 1==0

        GOAL = new_state
        train_data = "GOAL " + GOAL.replace("\n"," ").replace("\t"," ").strip() + " PROOFSTEP " + PROOFSTEP
        if name_count != 9:
              all_train_datas.append(train_data)
        else:
              all_valid_datas.append(train_data)
    name_count += 1

print("name_count:{}".format(name_count))

all_train_datas = list(set(all_train_datas))
train_datas_str = "\n".join(all_train_datas)
with open("train_txt_step2_remove_this.txt","w") as file:
    file.write(train_datas_str)

all_valid_datas = list(set(all_valid_datas))
valid_datas_str = "\n".join(all_valid_datas)
with open("valid_txt_step2_remove_this.txt","w") as file:
    file.write(valid_datas_str)