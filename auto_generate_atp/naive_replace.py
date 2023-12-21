from sympy import *
from copy import deepcopy


# m_ws: {a:-2, b:1/4}; expr: a*sin(b*x) ==> -2*sin(1/4*x)
def fill_back(m_ws, expr):
    return expr.xreplace(m_ws)


# 要求匹配上的值全是数值; 不能是分数形式 如 a: 1/sin(x) 或者 cos(x)/sin(x)
def good_match(values):
    for value in values:
        if value.is_Pow and value.exp < 0:
            return False

        if not good_match(list(value.args)):
            return False

    return True


def wild_match(expr_orig, old, new):
    if expr_orig.match(old):
        m_ws = expr_orig.match(old)
        if not good_match(m_ws.values()):
            return expr_orig
        rv = fill_back(m_ws, new)
        return rv
    return expr_orig


def check_match(expr_orig, old, new):
    expr = wild_match(expr_orig, old, new)
    if expr != expr_orig:
        return True, expr
    else:
        return False, expr


# 检查表达式里面是有通配符
def check_has_wild(expr):
    if isinstance(expr, int) or isinstance(expr, float):
        return False

    for arg in expr.args:
        if isinstance(arg, Wild):
            return True
        elif isinstance(arg, Symbol):
            continue
        else:
            if check_has_wild(arg):
                return True
    return False


# 后处理c/d 匹配 (1-cos(x)) / sin(x) 出现的问题；未开发完成
def post_process_ms(expr, ms):
    if expr.is_Mul:
        # 检查是否为分数，并且把分子和分母抽取出来
        (expr.args[0].is_Pow and expr.args[0].exp == -1)
        # 检查分子和分母是否为 pow(*, -1)的形式，如果是 则重新复制；


def merge_dict(dict1, dict2):
    new_dict = dict()
    if dict1:
        for key, value in dict1.items():
            new_dict[key] = value

    if dict2:
        for key, value in dict2.items():
            new_dict[key] = value
    return new_dict


def step_replace(expr_orig, old, new):
    # 针对1 = sin(x) ** 2 + cos(x) ** 2类似情况、
    # 单函数(如sin(2*x)=2*sin(x)*cos(x))替换;
    if isinstance(old, int) or isinstance(old, float)\
            or old.is_Function == 1 or old.is_Integer or old.is_Pow or len(old.args)==0:
        return expr_orig.replace(old, new)

    m_cnt = 0
    m_ind = []
    m_o_ind = []
    is_replaced = False
    m_ws = None
    has_wild = check_has_wild(old)

    # 无通配符情况较为简单；通配符实现目前可能存在一些问题
    if has_wild:
        if expr_orig.is_Function or (expr_orig.is_Pow and old.is_Pow):
            return wild_match(expr_orig, old, new)

        for ind, arg in enumerate(expr_orig.args):
            if isinstance(arg, Symbol) or isinstance(arg, Rational)\
                    or arg.is_NumberSymbol:
                continue

            is_success, expr = check_match(expr_orig, old, new)
            if is_success:
                return expr

            # 通配符只有加的情况下，才能采取分开匹配模型；
            if old.is_Add:
                for ind_, o_arg in enumerate(old.args):
                    if isinstance(arg, Symbol) \
                            or type(o_arg) != type(arg):
                        continue

                    if arg.match(o_arg) and ind_ not in m_o_ind:
                        m_ws = merge_dict(m_ws, arg.match(o_arg))
                        m_cnt += 1
                        m_ind.append(ind)
                        m_o_ind.append(ind_)
                        break
    else:
        if not ((expr_orig.is_Mul and old.is_Mul) or (expr_orig.is_Add and old.is_Add)):
            return expr_orig


        for ind, expr_arg in enumerate(expr_orig.args):
            for old_arg in old.args:
                if expr_arg == old_arg:
                    m_cnt += 1
                    m_ind.append(ind)

    # 如果匹配上old表达式，用new表达式替换
    args_lis = list(expr_orig.args)
    if m_cnt == len(old.args):
        for o_ind in m_ind:
            args_lis[o_ind] = None

            if not is_replaced:
                args_lis[o_ind] = new
                is_replaced = True

                # 如果通配符匹配上
                if m_ws:
                    args_lis[o_ind] = fill_back(m_ws, new)

        # Remove the None
        new_args_lis = []
        for arg in args_lis:
            if arg:
                new_args_lis.append(arg)

        if expr_orig.is_Mul:
            rv = Mul(*[_f for _f in new_args_lis if _f])
        else:
            rv = Add(*[_f for _f in new_args_lis if _f])
        return rv
    else:
        return expr_orig


def bottom_up(rv, F, old, new, atoms=False, nonbasic=False):
    """Apply ``F`` to all expressions in an expression tree from the
    bottom up. If ``atoms`` is True, apply ``F`` even if there are no args;
    if ``nonbasic`` is True, try to apply ``F`` to non-Basic (what?) objects.
    """
    args = getattr(rv, 'args', None)
    if args is not None:
        if args:
            args = tuple([bottom_up(a, F, old, new, atoms, nonbasic) for a in args])
            if args != rv.args:
                rv = rv.func(*args)
            else:
                rv = F(rv, old, new)
        elif atoms:
            rv = F(rv, old, new)
    else:
        if nonbasic:
            try:
                rv = F(rv, old, new)
            except TypeError:
                pass
    return rv


# atoms=True; 针对1=sin(x)**2+cos(x)**2类似情况
def perform(expr_orig, old, new, atoms=False, silent=True):
    if not silent:
        print("expr_orig:", expr_orig)
        print("old:", old)
        print("new:", new)
    raw_expr_orig = deepcopy(expr_orig)
    expr_new = bottom_up(expr_orig, step_replace, old, new, atoms=atoms)
    if expr_new == raw_expr_orig:
        expr_new = bottom_up(raw_expr_orig, step_replace, 1/old, 1/new, atoms=atoms)
    return expr_new

if __name__ == "__main__":
    x, y, z = symbols('x y z')
    #
    # a = (-cos(x)-sin(x))*sin(x) +1
    # b = normalize_negative_term(a)
    # print(b)

    ### Example #22 #####
    expr = (3+cos(x))*(sin(x)*tan(x))/((3/2+cos(x)/2)*(cot(x)))
    old = (3+cos(x))/(3/2+cos(x)/2)
    new = parse_expr("1/2")
    after = perform(expr, old, new, atoms=True)
    print(after)
    print(after.args)
    print(after.func)
    print(after.func(*after.args))
    # -sin(x)**3 - sin(x)*cos(x)**2 = -(sin(x)**2 + cos(x)**2)*sin(x)
    # print(bottom_up(expr_orig, step_replace, old, new))


    ### Example#1  #######
    # expr_orig = sin(x)**2 + cos(x)**2 + 0.2
    # old = cos(x)**2 + sin(x)**2
    # new = y

    # expr_orig = 1/2 * sin(x)**2 + 1/2*cos(x)**2 + 0.2
    # old = 1/2*cos(x)**2 + 1/2*sin(x)**2
    # new = 0.5

    #### Example#2 ########
    # expr_orig = sin(x) + sin(y) + 1
    # old = sin(x) + 1
    # new = 2*sin(x/2)*cos(x/2) + 1


    #### Example#3  ######
    # 带系数的替换；如：2*sin(2x) -> 4*sin(x)*cos(x)  expr_orig 中x换成2*x会出现bug
    # expr_orig = (2*sin(x) + 1) * sin(x) + sin(2*x)
    # old = sin(x)
    # new = 2*sin(x/2)*cos(x/2)
    #


    #### Example#3  ######
    # expr_orig = (-2*sin(x/2)**2 - 2*cos(x/2)**2 + 2)*sin(x/2)
    # old = -2*cos(x/2)**2 + -2*sin(x/2)**2
    # new = -2


    ##### Example#4 ########


    #### Example#5 ##########
    # expr_orig = (-2*sin(x/2)**2 - 2*cos(x/2)**2 + 2)*sin(y/2)*cos(y/2) + (-2*sin(y/2)**2 - 2*cos(y/2)**2 + 2)*sin(x/2)*cos(x/2)
    # old = -2*cos(x/2)**2 - 2*sin(x/2)**2
    # new = -2

    # perform(expr, old, new)

    # from sympy import Wild
    # a = Wild('a')
    # b = Wild('b')
    # c = Wild('c')
    # d = Wild('d')

    ### Example#6  ######
    # expr_orig = (-2*sin(x/2)**2 - 2*cos(x/2)**2 + 2)*sin(x/2) + 1/3*cos(x/3)**2 + 1/3*sin(x/3)**2
    # old = a*cos(b*x)**2 + a*sin(b*x)**2
    # new = a

    ### Example#7 ######
    # expr_orig = 3*sin(x) + cos(x)
    # old = a*sin(x)
    # new = 2*a*sin(x/2)*cos(x/2)

    ### Example#8 ######
    # expr_orig = 3*sin(x) + cos(x) + sin(x) * cos(x) * (1 + sin(3*x))
    # old = sin(x)
    # new = 2*sin(x/2)*cos(x/2)


    ### Example#9 ######
    # expr_orig = sin(pi/9)**2 + 1
    # old = sin(a)**2
    # new = 1/2*(1-cos(2*a))

    ### Example#10 #####
    # expr_orig = (sin(x)**2 + 3) * sin(x)**2
    # old = sin(x)**2
    # new = 1/2*(1-cos(2*x))

    ### Example#11 #####
    # expr_orig = sin(5 * x) + sin(2*x) + 1 + sin(-3*x)
    # old = sin(a * x)
    # new = sin((a - 1) * x) * cos(x) + sin(x) * cos((a - 1) * x)
    #
    # ### Example#12 ####
    # expr_orig = tan(x) ** 2 + tan(x)
    # old = tan(x)
    # new = sin(x) / cos(x)
    #


    #### Example#13 #####
    # expr_orig = sin(x) / (1 - cos(x)) - (1 + cos(x)) / sin(x)
    # old = a/b + c/d
    # new = (a*d + b*c)/(b*d)
    # match_inds = {}


    #### Example#14 #####
    # expr_orig = (sin(4*pi/9) - sqrt(3)*sin(pi/18))/cos(7*pi/18)
    # old = (a + b)/c
    # new = 2*(1/2*a + 1/2*b)/c


    ### Example#15 ####
    # expr_orig = cos(x+pi/4)
    #
    # old = a + b
    # new = cos(x)

    ### Example#16 ####
    # expr_orig = cos(2*x) + 1
    # old = cos(2*x)
    # new = -cos(pi + 2*x)

    ### Example#17 ####
    # expr_orig = 2*sqrt(3)/2
    # old = sin(x)
    # new = 2*sin(x/2)*cos(x/2)

    ### Example#18 ####
    # expr_orig = sin(pi/4)
    # old = cos(pi/4)
    # new = sin(pi/3)


    ### Example#17 ####
    # expr_orig = sqrt(1+2*sin(2)*cos(2))
    # old = 1
    # new = sin(2)**2 + cos(2)**2


    ### Example#18 ####
    # expr_orig = (-sin(x)**2 + cos(x)**2 + 1)*sin(x) / cos(x)**2 - 2*sin(x)
    # old = 1
    # new = sin(x)**2 + cos(x)**2


    ### Example #19 #####
    # 替换出现bug；输出：sin(pi/6)/(cos(pi/18)*cos(pi/9)) + sin(pi/6)*tan(pi/3)/(cos(pi/18)*cos(pi/9)) bug 解决
    # expr_orig = tan(pi/18)*tan(pi/9) + (tan(pi/18) + tan(pi/9))*tan(pi/3)
    # old = tan(pi/18) + tan(pi/9)
    # new = sin(pi/18 + pi/9) / (cos(pi/18) * cos(pi/9))

    #### Example #20 #####
    # expr_orig = sin(x)*sin(x - pi/3) + cos(x)*cos(x - pi/3)
    # old = 1
    # new = 321


    ### Example #21 #####
    # expr_orig = sqrt(9)*sin(pi/4)
    # old = sin(pi/4)
    # new = sqrt(2)/2


    ### Example #22 #####
    # expr_orig = sin(5*pi/6)*sin(pi) + cos(5*pi/6)*cos(pi)
    # old = cos(5*pi/6)*cos(pi) + sin(5*pi/6)*sin(pi)
    # new = cos(pi - 5*pi/6)

    # expr_orig = sqrt(27) * sqrt(27)

    # print(bottom_up(expr_orig, step_replace, old, new))


