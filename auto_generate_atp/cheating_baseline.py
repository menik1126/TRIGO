from lean_server import LeanServer
import pandas as pd

def match_proofstep_data():
    lean_gym = LeanServer()
    data_df = pd.read_csv('datasets/cleaned_training_data/data_and_metadata.csv')
    current_dec_name = None
    breaked_dec_name = None
    current_ts = None
    result = []
    cur_result = []
    total_cnt = 0
    correct_cnt = 0
    for idx, row in data_df.iterrows():
        if row['Unnamed: 0'] != idx:
            print('csv error')
            continue
        # goal might be Nan in original csv file.
        # goal = row['cleaned_goal'].replace('\n', ' ').replace('\t',' ').strip()
        tactic = row['human_tactic_code']
        dec_name = row['decl_name']
        name_space = row['open_namespaces']

        if dec_name == breaked_dec_name:
            continue
        else:
            breaked_dec_name = None

        if current_dec_name is None:
            current_ts = lean_gym.init_search(dec_name=dec_name, namespaces=name_space)
            total_cnt += 1
            if current_ts['error'] is None:
                # add intros
                current_ts = lean_gym.run_tac(current_ts['search_id'], current_ts['tactic_state_id'], 'try {intros}')
                current_dec_name = dec_name
            else:
                breaked_dec_name = dec_name
            
        if current_dec_name is not None:
            past_ts = current_ts
            current_ts = lean_gym.run_tac(past_ts['search_id'], past_ts['tactic_state_id'], tactic)
            if current_ts['error'] is None:
                cur_result.append({
                    'tactic_state': past_ts['tactic_state'],
                    'human_tactic_code': tactic,
                    'dec_name': row['decl_name'],
                    'open_namespaces': row['open_namespaces'],
                    'split': row['split'],
                    'filename': row['filename'],
                    'line': row['line'],
                    'column': row['column'],
                    'proof_key': row['proof_key'],
                    'tactic_class': row['tactic_class'],
                    'goal_pp': row['goal_pp'],
                    'cleaned_goal': row['cleaned_goal']
                })
            else:
                cur_result = []
                current_dec_name = None
                lean_gym.clear_search(past_ts['search_id'])
                breaked_dec_name = dec_name
                continue
            if current_ts['tactic_state'] == 'no goals':
                result.extend(cur_result)
                cur_result = []
                current_dec_name = None
                lean_gym.clear_search(current_ts['search_id'])
                correct_cnt += 1
        print(f"{correct_cnt} / {total_cnt}, {correct_cnt / total_cnt}, {past_ts['search_id']}")
    pd.DataFrame(result).to_csv('out.csv')

if __name__ == '__main__':
    match_proofstep_data()