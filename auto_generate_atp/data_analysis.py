import json
from turtle import distance
from matplotlib import pyplot as plt
from matplotlib.image import imsave
import numpy as np
import pandas as pd
from tqdm import tqdm
pd.options.mode.chained_assignment = None  # default='warn'
from pprint import pprint
import scipy.stats as stats
# fname = 'filtered_training_data/filtered_train.names'

# with open(fname) as f:
#     lines = f.readlines()

# d = {}
# for line in lines:
#     region = line.split('.')[0]
#     if region in d:
#         d[region] += 1
#     else:
#         d[region] = 1


def cal_branches(df, cleaned_names):
    df['in_cleaned'] = df['decl_name'].isin(set(cleaned_names))

    def get_cat(path):
        if 'mathlib/src/' in path:
            path = path[12: ]
            path = path[:path.find('/')]
            path = 'mathlib/src/' + path
        elif 'lean/library/' in path:
            path = path[13: ]
            path = path[:path.find('/')]
            path = 'lean/library/' + path

        return path

    df['cat'] = df['filename'].map(get_cat)

    cat_list = df['cat'].unique().tolist()

    # cleaned
    # df = df[df['in_cleaned'] == True]

    train_df = df[df['split'] == 'train']
    test_df = df[df['split'] == 'test']
    valid_df = df[df['split'] == 'valid']

    count = df.groupby(['cat','decl_name'])['cleaned_goal'].count()
    count_train = train_df.groupby(['cat','decl_name'])['cleaned_goal'].count()
    count_test = test_df.groupby(['cat','decl_name'])['cleaned_goal'].count()
    count_valid = valid_df.groupby(['cat','decl_name'])['cleaned_goal'].count()



    d = {}
    for cat in cat_list:
        try:
            d[cat] = [len(count[cat].keys()), 0,0,0]
        except:
            d[cat] = [0,0,0,0]

    for cat in cat_list:
        try:
            d[cat][1] = len(count_train[cat].keys())
        except:
            d[cat][1] = 0

    for cat in cat_list:
        try:
            d[cat][2] = len(count_test[cat].keys())
        except:
            d[cat][2] = 0

    for cat in cat_list:
        try:
            d[cat][3] = len(count_valid[cat].keys())
        except:
            d[cat][3] = 0

    total, train, test, valid = 0,0,0,0
    for k, v in d.items():
        print(f'{k:50}{v}')
        total+= v[0]
        train+= v[1]
        test+=v[2]
        valid+=v[3]

    print("total, train, test, valid", total, train, test, valid)

def cal_length(df, cleaned_names):
    result = {}
    
    decl_names = df['decl_name'].unique().tolist()
    for name in tqdm(decl_names):
        proofstep_df = df[df['decl_name'] == name]
        if proofstep_df.iloc[0]['split'] == 'train':
            continue
        proofstep_df['tl'] = proofstep_df['human_tactic_code'].apply(len)
        proofstep_df = proofstep_df.sort_values(['tl'])
        proofstep_df = proofstep_df.drop_duplicates(subset=['cleaned_goal'])
        result[name] = sum(proofstep_df['tl'].tolist())
    with open('result_length.json', 'w') as fp:
        json.dump(result, fp)
    values = result.values()
    values = np.asarray(values)
    plt.hist(values)
    plt.imsave('out.png')


def cal_knn(retrieval, knn=10):
    result = {}
    df = pd.read_csv('datasets/cleaned_training_data/data_and_metadata.csv')
    decl_names = df['decl_name'].unique().tolist()
    for name in tqdm(decl_names):
        proofstep_df = df[df['decl_name'] == name]
        if proofstep_df.iloc[0]['split'] == 'train':
            continue
        proofstep_df['tl'] = proofstep_df['human_tactic_code'].apply(len)
        proofstep_df = proofstep_df.sort_values(['tl'])
        proofstep_df = proofstep_df.drop_duplicates(subset=['cleaned_goal'])
        query = []
        for _, row in proofstep_df.iterrows():
            if isinstance(row['cleaned_goal'], str):
                text = 'DEC ' + row['decl_name'] + ' GOAL ' + row['cleaned_goal'] + ' PROOFSTEP '
                query.append(text.replace('\t', ' '))
        distances, _ =  retrieval.search_knn(query, knn)
        result[name] = distances.mean(0)[:5].mean().item()
    # json_object = json.dumps(result, indent = 4) 
    with open('result_distance.json', 'w') as fp:
        json.dump(result, fp)
    values = result.values()
    values = np.asarray(list(values))
    plt.hist(values, bin=1000)
    plt.imsave('out_distance.png')

def cal_overall():
    with open('result_distance.json', 'r') as fp:
        result_distance = json.loads(fp.readline())
    with open('result_length.json', 'r') as fp:
        result_length = json.loads(fp.readline())

    l = np.asarray(list(result_length.values()))
    d = np.asanyarray(list(result_distance.values()))
    d[d>86] = 86.0
    l = np.log(l)
    l = (l - l.min()) / (l.max() - l.min())
    d = (d - d.min()) / (d.max() - d.min())
    f = 0.5 * l + 0.5 * d
    is_valid = []
    with open('datasets/cleaned_training_data/test.names', 'r') as fp:
        test_names = fp.readlines()
        test_names = [n.strip().split()[0] for n in test_names]
        for name in result_length.keys():
            if name in test_names:
                is_valid.append(False)
            else:
                is_valid.append(True)
    test_f = f[~np.asarray(is_valid)]
    valid_f = f[np.asarray(is_valid)]
    plt.hist(f, bins=60, fc=(0, 1, 0, 0.5),label='total')
    # density = stats.gaussian_kde(test_f)
    n, valid_x , _ = plt.hist(valid_f, bins=60, fc=(1, 0, 0, 0.5),label='valid')
    n, test_x, _ = plt.hist(test_f, bins=60, fc=(0, 0, 1, 0.5),label='test')
    
    # plt.plot(test_x, density(test_x))
    plt.xlabel('complexity', fontsize=18)
    plt.ylabel('number of theorems', fontsize=16)
    # plt.title('theorem complxity histogram',fontsize=20)
    plt.xticks(size = 13)
    plt.yticks(size = 13)
    plt.legend()
    # plt.subplots_adjust(left=0.13, right=0.98, bottom=0.13, top=0.90)
    plt.savefig('f.png',dpi=300, bbox_inches = "tight")


        
    print(len(result_distance))
    print(len(result_length))
    

if __name__=='__main__':    

    cal_overall()

    cleaned_names = []

    with open('datasets/filtered_training_data/filtered_multi_train.names') as names:
        lines = names.readlines()
        for line in lines:
            decl_nm = line.split()[0]
            cleaned_names.append(decl_nm)

    with open('datasets/filtered_training_data/filtered_test.names') as names:
        lines = names.readlines()
        for line in lines:
            decl_nm = line.split()[0]
            cleaned_names.append(decl_nm)

    with open('datasets/filtered_training_data/filtered_valid.names') as names:
        lines = names.readlines()
        for line in lines:
            decl_nm = line.split()[0]
            cleaned_names.append(decl_nm)


    # cal_branches(df, cleaned_names)
    df = pd.read_csv('datasets/cleaned_training_data/data_and_metadata.csv')
    cal_length(df, cleaned_names)