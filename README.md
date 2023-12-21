# TRIGO
"Open-source code for TRIGO: Benchmarking Formal Mathematical Proof Reduction for Generative Language Models" accepted by the main conference of EMNLP 2023.


## Requirments
sympy == 1.7.1

## Installation of elan and Lean3
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source $HOME/.elan/env  
python3 -m pip install mathlibtools  
cd auto_generate_atp/lean_gym  
bash scripts/setup.sh

## Initialize lean-gym
cd auto_generate_atp/lean_gym  
lean --make src

## Generate lemmas from random rules
python generate_lemma_from_rule.py

## Generating lemmas from Problems in the Real World
python generate_lemma_from_trigo.py

## Generate more complex combinations of numbers, typically these numbers are sampled from a range that is larger than the range of the original generated data.
python generate_lemma_from_rule_generalizaiton_number.py

## Merge the generated data into a Lean file and remove redundant proof steps.
cd generated_data  
python generate_and_emerge_data_from_rules.py  
cd ..  
python delete_useless_data_step1.py

## Generate the final proofs.
python generate_train_data_step1.py


