from transformers import GPT2LMHeadModel, GPT2TokenizerFast
import torch
from tqdm import tqdm
import argparse


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--device', default='0', type=str,
                        required=False, help='设置使用哪些显卡')
    parser.add_argument('--raw_data_path', default='data/test.txt',
                        type=str, required=False, help='原始语料')
    parser.add_argument('--stride', default=128, type=int,
                        required=False, help='取数据的窗口步长')
    parser.add_argument('--pretrained_model', default='model0330/model_epoch2',
                        type=str, required=False, help='模型起点路径')
    parser.add_argument('--model_type', default='gpt2-medium',
                        type=str, required=False, help='模型起点路径')


    args = parser.parse_args()
    print('args:\n' + args.__repr__())

    device = f"cuda:{args.device}"
    model_id = args.model_type
    pretrained_model_path = args.pretrained_model
    model = GPT2LMHeadModel.from_pretrained(pretrained_model_path).to(device)
    tokenizer = GPT2TokenizerFast.from_pretrained(model_id)
    max_length = 256
    

    def cal_ppl(texts, stride = 512):
        encodings = tokenizer(texts, return_tensors="pt")
        nlls = []
        for i in (pbar := tqdm(range(0, encodings.input_ids.size(1), stride))):
            begin_loc = max(i + stride - max_length, 0)
            end_loc = min(i + stride, encodings.input_ids.size(1))
            trg_len = end_loc - i  # may be different from stride on last loop
            input_ids = encodings.input_ids[:, begin_loc:end_loc].to(device)
            target_ids = input_ids.clone()
            target_ids[:, :-trg_len] = -100

            with torch.no_grad():
                outputs = model(input_ids, labels=target_ids)
                neg_log_likelihood = outputs[0] * trg_len

            nlls.append(neg_log_likelihood)
            current_ppl = torch.exp(torch.stack(nlls).sum() / end_loc).item()
            pbar.set_description("Cur ppl %.5f" % current_ppl)

        ppl = torch.exp(torch.stack(nlls).sum() / end_loc)
        print(f'Text ppl is {ppl}')
        return ppl

    with open('data/valid.txt', 'r') as f:
        texts = f.readlines()
        print(f'Num of texts: {len(texts)}')
        cal_ppl("\n\n".join(texts), args.stride)


if __name__ == '__main__':
    main()
    