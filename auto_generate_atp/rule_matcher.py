import sys
sys.path.insert(0, "..")
from sympy import *
from copy import deepcopy

#TODO: 对于数字的match还需要检查正确性！！！


TRIGO_FUNC_LIST = [sin, cos, tan, sec, csc, cot]

def isNumber_or_Pi_or_sym(expr):
    #含有三角函数的一律不算常数
    if expr.func in TRIGO_FUNC_LIST:
        return False
    #当前func不是三角函数，判断是否所有args都是常数
    if isinstance(expr, float) or isinstance(expr, int):
        return True

    if len(expr.args) == 0:
        if not (expr.is_Number or expr == pi or expr.is_Symbol):
            return False
        return True
    else:
        for arg in expr.args:
            if not isNumber_or_Pi_or_sym(arg):
                return False
        return True


def isNumber_or_Pi(expr):
    #含有三角函数的一律不算常数
    if expr.func in TRIGO_FUNC_LIST:
        return False
    #当前func不是三角函数，判断是否所有args都是常数
    if isinstance(expr, float) or isinstance(expr, int):
        return True

    if len(expr.args) == 0:
        if not (expr.is_Number or expr == pi):
            return False
        return True
    else:
        for arg in expr.args:
            if not isNumber_or_Pi(arg):
                return False
        return True

def check_free_symbol(exp):
    '''
    检查是不是与变量项，例如X， pi/2-X, X + Y
    '''
    #情况1：单变量
    if exp.is_Symbol:
        return True
    #情况2：带X的加（减）或乘(除)
    if not (exp.is_Add or exp.is_Mul):
        return False
    for arg in exp.args:
        if arg.is_Symbol or (-arg).is_Symbol or (1/arg).is_Symbol or check_free_symbol(arg):
            return True
    return False


def search_matching(arg_match_list, cur_matched, success):
    cur_id = len(cur_matched)
    if cur_id == len(arg_match_list):  #所有项都已经成功匹配，将该匹配方案加入到success列表中
        success.append(deepcopy(cur_matched))
        return

    #开始为第cur_id项进行匹配
    this_matching = arg_match_list[cur_id]
    for match_arg in this_matching.keys():
        if match_arg in cur_matched:  #这一项已经被匹配过了，跳过这一项
            continue
        #这一项没有被匹配过，加入到cur_matched中，递归搜索下一层
        cur_matched.append(match_arg)
        search_matching(arg_match_list, cur_matched, success)
        cur_matched.pop()  #搜索完成，回溯，将该项匹配取消
    return

def equation_combine(pre_eq, cur_eq):
    if 'coef' not in cur_eq:
        cur_eq['coef'] = 1
    if pre_eq is None:
        new_eq = {}
    else:
        new_eq = deepcopy(pre_eq)
        if "coef" not in new_eq:
            new_eq['coef'] = 1
    for key, value in cur_eq.items():
        if key not in new_eq:
            new_eq[key] = value
        elif new_eq[key] != value:
            return False, {}
    if 'coef' in new_eq and new_eq['coef'] == 1:
        new_eq.pop('coef')
    return True, new_eq


def get_coef(exp):
    if not exp.is_Mul:
        return 1
    coef = 1
    for arg in exp.args:
        if isNumber_or_Pi(arg):
            coef = coef*arg
    return coef

# def simple_rule_match_no_symbol(orig, rule, exact=True, constant_coef=False):
#     '''
#     在当前level进行匹配，可以相差常数系数，并假设orig不包含变量，且rule中变量只替换成数值
#     如果exact=True，则要求必须完全匹配，即每项一一对应，且不带有常数系数
#     否则，只需要rule中的每一项都被匹配即可，且可以相差常数系数
#     返回match之后的结果，以及rule中变量的取值字典
#     '''
#     if rule.is_Number:
#         if constant_coef:
#             if isNumber_or_Pi(orig):
#                 return True, [{'coef': orig/rule}]
#         if orig == rule:
#             return True, [{}]
#         else:
#             return False, []
#
#     if constant_coef:
#         orig_coef = get_coef(orig)
#         rule_coef = get_coef(rule)
#         orig = orig/orig_coef
#         rule = rule/rule_coef
#         coef = orig_coef/rule_coef
#         if coef == 1:
#             constant_coef=False
#
#     if check_free_symbol(rule):  #rule 是变量项，应当匹配数值
#         if not isNumber_or_Pi(orig):
#             return False, []
#         #rule是变量， 且orig是数值，建立等式 rule = orig 求解变量
#         if len(rule.free_symbols)==1:  #如果单变量，直接用solveset求解
#             answer = solveset(Eq(rule, orig)).args
#             if len(answer)>1:  #如果有多解，暂不处理
#                 raise NotImplementedError("multiple matches for a single variable?")
#             if len(answer) == 0:  #如果无解，则返回匹配失败
#                 return False, []
#             return True, [{list(rule.free_symbols)[0]: answer[0]}]
#         else:  #如果多变量，暂不求解，将方程返回
#             return True, [{rule: orig}]
#
#     #要在当前level匹配，首先要求func一致
#     if orig.func != rule.func:
#         return False, []
#     #其次对args进行匹配，要求orig的args数量不少于rule（至少可以覆盖）
#     if len(orig.args) < len(rule.args):
#         return False, []
#     #如果是exact，那么要求两者的args数量一致
#     if exact and (len(orig.args) != len(rule.args)):
#         return False, []
#
#     #接下来搜索rule的每一个arg能和orig中哪些arg匹配
#     rule_args_matching_list = []
#     #list of n term, n is the num of rule args
#     #each term is a dictionary, keys: matched orig arg id, values: list of equation sets
#     for rule_idx, rule_arg in enumerate(rule.args):
#         rule_matched = {}
#         for orig_idx, orig_arg in enumerate(orig.args):
#             if not exact and rule.is_Add:
#                 match_success, sym_eq_dict = simple_rule_match(orig_arg, rule_arg, exact=True, constant_coef=True)
#             else:
#                 match_success, sym_eq_dict = simple_rule_match(orig_arg, rule_arg, exact=True)
#             if match_success:
#                 rule_matched[orig_idx] = sym_eq_dict
#         rule_args_matching_list.append(rule_matched)
#
#     success_list = []
#     search_matching(rule_args_matching_list, [], success_list)
#     if len(success_list) == 0:
#         return False, []
#
#     #对所有success的匹配进行求解
#     all_match = []
#     for match_map in success_list:
#         all_eq_list = [{}]
#         #遍历该success的匹配中的所有方程并组合
#         for idx, rule_args_match in enumerate(rule_args_matching_list):
#             cur_eq_list = rule_args_match[match_map[idx]]  # rule中第idx项对应到orig的 match_map[idx],得到的方程组列表为cur_eq
#             new_all_eq_list = []  #存储更新后的方程组列表
#             #遍历之前可能的方程组与当前的方程组，两两合并，将成功的例子加入到更新后方程组列表
#             for cur_eq in cur_eq_list:
#                 for all_eq in all_eq_list:
#                     success, result = equation_combine(all_eq, cur_eq)
#                     if success:
#                         new_all_eq_list.append(result)
#             all_eq_list = new_all_eq_list  #更新方程组，进入下一项匹配
#         # all_eq_list 包含了当前success 匹配对应的所有可能方程组
#         all_match += all_eq_list
#
#     if constant_coef:
#         for d in all_match:
#             d['coef'] = coef
#     if all_match:
#         return True, all_match
#     else:
#         return False, []


def simple_rule_match(orig, rule, exact=True, constant_coef=False):
    '''
    在当前level进行匹配，可以相差常数系数，并假设orig不包含变量，且rule中变量只替换成数值
    如果exact=True，则要求必须完全匹配，即每项一一对应，且不带有常数系数
    否则，只需要rule中的每一项都被匹配即可，且可以相差常数系数
    返回match之后的结果，以及rule中变量的取值字典
    '''
    if rule.is_Number:
        if constant_coef:
            if isNumber_or_Pi(orig):
                return True, [{'coef': orig/rule}]
        if orig == rule:
            return True, [{}]
        else:
            return False, []

    if constant_coef:
        orig_coef = get_coef(orig)
        rule_coef = get_coef(rule)
        orig = orig/orig_coef
        rule = rule/rule_coef
        coef = orig_coef/rule_coef
        if coef == 1:
            constant_coef=False

    if check_free_symbol(rule):  #rule 是变量项，应当匹配数值
        if not isNumber_or_Pi_or_sym(orig):
            return False, []
        #rule是变量， 且orig是数值，建立等式 rule = orig 求解变量
        if len(rule.free_symbols)==1:  #如果单变量，直接用solveset求解
            answer = solveset(Eq(rule, orig),list(rule.free_symbols)[0]).args
            if len(answer)>1:  #如果有多解，暂不处理
                raise NotImplementedError("multiple matches for a single variable?")
            if len(answer) == 0:  #如果无解，则返回匹配失败
                return False, []
            return True, [{list(rule.free_symbols)[0]: answer[0]}]
        else:  #如果多变量，暂不求解，将方程返回
            return True, [{rule: orig}]

    #要在当前level匹配，首先要求func一致
    if orig.func != rule.func:
        return False, []
    #其次对args进行匹配，要求orig的args数量不少于rule（至少可以覆盖）
    if len(orig.args) < len(rule.args):
        return False, []
    #如果是exact，那么要求两者的args数量一致
    if exact and (len(orig.args) != len(rule.args)):
        return False, []

    #接下来搜索rule的每一个arg能和orig中哪些arg匹配
    rule_args_matching_list = []
    #list of n term, n is the num of rule args
    #each term is a dictionary, keys: matched orig arg id, values: list of equation sets
    for rule_idx, rule_arg in enumerate(rule.args):
        rule_matched = {}
        for orig_idx, orig_arg in enumerate(orig.args):
            if not exact and rule.is_Add:
                match_success, sym_eq_dict = simple_rule_match(orig_arg, rule_arg, exact=True, constant_coef=True)
            else:
                match_success, sym_eq_dict = simple_rule_match(orig_arg, rule_arg, exact=True)
            if match_success:
                rule_matched[orig_idx] = sym_eq_dict
        rule_args_matching_list.append(rule_matched)

    success_list = []
    search_matching(rule_args_matching_list, [], success_list)
    if len(success_list) == 0:
        return False, []

    #对所有success的匹配进行求解
    all_match = []
    for match_map in success_list:
        all_eq_list = [None]
        #遍历该success的匹配中的所有方程并组合
        for idx, rule_args_match in enumerate(rule_args_matching_list):
            cur_eq_list = rule_args_match[match_map[idx]]  # rule中第idx项对应到orig的 match_map[idx],得到的方程组列表为cur_eq
            new_all_eq_list = []  #存储更新后的方程组列表
            #遍历之前可能的方程组与当前的方程组，两两合并，将成功的例子加入到更新后方程组列表
            for cur_eq in cur_eq_list:
                for all_eq in all_eq_list:
                    success, result = equation_combine(all_eq, cur_eq)
                    if success:
                        new_all_eq_list.append(result)
            all_eq_list = new_all_eq_list  #更新方程组，进入下一项匹配
        # all_eq_list 包含了当前success 匹配对应的所有可能方程组
        for i in range(len(all_eq_list)):
            cur_eq = all_eq_list[i]
            if cur_eq is None:
                all_eq_list[i] = {}
        all_match += all_eq_list

    if constant_coef:
        for d in all_match:
            if d is None:
                d = {}
            d['coef'] = coef
    if all_match:
        return True, all_match
    else:
        return False, []

# def bottom_up_rule_match(orig, rule):
#     result = []
#     args = getattr(orig, 'args', None)
#     if args is None:
#         return simple_rule_match(orig, rule)
#     #遍历args进行匹配
#     # print("args:{}".format(args))
#     for arg in args:
#         tmp_result = bottom_up_rule_match(arg, rule)
#         result += tmp_result

#     success, tmp_result = simple_rule_match(orig, rule, exact=False)
#     if success:
#         result += tmp_result
#     return result

def solve_eq(eq_dict, unknown_list):
    if len(unknown_list) == 0:
        return [{}]
    eq_list = [left - right for left, right in eq_dict.items()]
    ans_list = list(linsolve(eq_list, unknown_list))
    all_ans_dict = []
    for ans in ans_list:
        ans_dict = {}
        has_free_solution = False
        for sym, value in zip(unknown_list, ans):
            ans_dict[sym] = value
            if sym == value:
                has_free_solution = True
                free_unk = sym

        if has_free_solution:
            continue
            # free_ans_list = []
            # #寻找free unknown 的方程
            # for k, v in ans_dict.items():
            #     if k != free_unk:  #从不是free unknown的value中寻找free unknown
            #         v_args = v.args
            #         free_arg = None
            #         for arg in v_args:
            #             if free_unk in arg.free_symbols:
            #                 free_arg = arg
            #         #free_arg 找到是的value中包含free unknown的项
            #         if free_arg is None:
            #             continue
            #         #和其他不包含free unknown的项建立方程并求解
            #         for arg in v_args:
            #             if free_unk not in arg.free_symbols:
            #                 eq = [free_arg + arg]
            #                 free_ans_list += list(linsolve(eq, [free_unk]))
            #
            # for free_ans in free_ans_list:
            #     free_subs = {free_unk: free_ans[0]}
            #     subs_ans_dict = {}
            #     for k, v in ans_dict.items():
            #         subs_ans_dict[k] = v.subs(free_subs)
            #     all_ans_dict.append(subs_ans_dict)
        else:
            all_ans_dict.append(ans_dict)

    return all_ans_dict

def symbol_match(orig, rule):
    if len(orig.free_symbols) != len(rule.free_symbols):
        return False, []
    orig_symbols = list(orig.free_symbols)
    rule_symbols = list(rule.free_symbols)
    if len(orig_symbols) == 1:
        free_sym = orig_symbols[0]
        rule_sym = rule_symbols[0]
        rule_mapped = rule.subs({rule_sym:free_sym})
        if rule_mapped == orig:
            return True, [{rule_sym:free_sym}]

    return False, []

def bottom_up_rule_match(orig, rule):
    #print("orig:{}".format(orig))
    result = []
    args = getattr(orig, 'args', None)
    if args is None:
        #print("here===============")
        return simple_rule_match(orig, rule)
    #遍历args进行匹配
    # print("args:{}".format(args))
    
    for arg in args:
        tmp_result = bottom_up_rule_match(arg, rule)
        result += tmp_result
    # print("orig:{}".format(orig))
    # print("rule:{}".format(rule))
    success, tmp_result = simple_rule_match(orig, rule, exact=False)
    if success:
        result += tmp_result
    return result

if __name__ == "__main__":
    x, y, X, Y, Z, K = symbols('x y X Y Z K')

    orig = sin(pi/3) + sin(pi/4)
    rule_left = sin(X) - sin(Y)
    #print("here=================================")
    # success, tmp_result = simple_rule_match(orig, rule_left, exact=False)
    result = bottom_up_rule_match(orig, rule_left)
    print(result)
    # print(success, tmp_result)
    # unknown_list = [X, Y]
    # for rule_map in result:
        # ans = solve_eq(rule_map, unknown_list)
        # print(ans)
