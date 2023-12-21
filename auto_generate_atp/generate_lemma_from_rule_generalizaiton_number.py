from sympy import *
import random
#from convert_mapped_rules_new import *
from rule_matcher import *
from naive_replace import *
from utils_trigo import get_denominators
import re

import sympy as sp

# 重新定义函数，用于仅化简三角函数内部的表达式
# 修改递归函数，以保持三角函数不变，即使它们的参数是常数
def simplify_pi_parts_without_evaluating_trig(expression):
    # 如果表达式是三角函数并且其参数包含 pi，则化简参数
    if isinstance(expression, (sp.sin, sp.cos, sp.tan)) and expression.args[0].has(sp.pi):
        simplified_arg = sp.simplify(expression.args[0])
        # 重新创建三角函数，而不计算其数值
        return expression.func(simplified_arg, evaluate=False)
    # 如果表达式不是原子表达式（即不可再分的部分），递归地处理其各个部分
    elif not expression.is_Atom:
        return expression.func(*[simplify_pi_parts_without_evaluating_trig(arg) for arg in expression.args])
    # 对于原子表达式，直接返回
    else:
        return expression

common_calc_steps = [
    # 'rw this',
    'focus{repeat {apply congr_arg _}}',
    'try {simp}',
    'ring'
]

class field_calc:
    def __init__(self):
        self.rule = "ABC"
        self.need_rule = True
        self.has_nonzero = True

    def get_tactics(self, mapping, left, right):
        simp_ignore = get_simp_ignore(left, right)
        if "sqrt" in left or "sqrt" in right:
            return [
                "try {ring_exp}",
                "try {rw sq_sqrt}",
                "try {field_simp " + simp_ignore + "}",
                "try {left}",
                "try {ring_exp}",
                "try {linarith}"
            ]
        return ["try {field_simp " + simp_ignore + "}", "try {left}", "try {ring_exp}"]

    def get_nonzero(self, mapping, left, right):
        denoms = list(set(get_denominators(left) + get_denominators(right)))
        return denoms

#replace const
class replace_const:
    def __init__(self):
        self.rule = "A=X"
        self.no_mapping = True
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        return ["try {field_simp}", "try {ring_exp}"]

#special angles begin
class sin_zero:
    def __init__(self):
        self.rule = "sin(0)=0"
        self.no_mapping = True
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        return ["rw sin_zero"]

class sin_pi:
    def __init__(self):
        self.rule = "sin(pi)=0"
        self.no_mapping = True
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        return ["rw sin_pi"]

class sin_two_pi_div_three:
    def __init__(self):
        self.rule = "sin(2*pi/3)=sqrt(3)/2"
        self.no_mapping = True
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        return ["rw sin_two_pi_div_three"]

class sin_three_pi_div_four:
    def __init__(self):
        self.rule = "sin(3*pi/4)=sqrt(2)/2"
        self.no_mapping = True
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        return ["rw sin_three_pi_div_four"]

class sin_five_pi_div_six:
    def __init__(self):
        self.rule = "sin(5*pi/6)=1/2"
        self.no_mapping = True
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        return ["rw sin_five_pi_div_six"]

class sin_pi_div_twelve:
    def __init__(self):
        self.rule = "sin(pi/12)=-sqrt(2)/4+sqrt(6)/4"
        self.no_mapping = True
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        return ["rw sin_pi_div_twelve"]

class sin_pi_div_two:
    def __init__(self):
        self.rule = "sin(pi/2)=1"
        self.no_mapping = True
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        return ["rw sin_pi_div_two"]

class sin_pi_div_three:
    def __init__(self):
        self.rule = "sin(pi/3)=sqrt(3)/2"
        self.no_mapping = True
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        return ["rw sin_pi_div_three"]

class sin_pi_div_four:
    def __init__(self):
        self.rule = "sin(pi/4)=sqrt(2)/2"
        self.no_mapping = True
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        return ["rw sin_pi_div_four"]

class sin_pi_div_six:
    def __init__(self):
        self.rule = "sin(pi/6)=1/2"
        self.no_mapping = True
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        return ["rw sin_pi_div_six"]

class cos_zero:
    def __init__(self):
        self.rule = "cos(0)=1"
        self.no_mapping = True
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        return ["rw cos_zero"]

class cos_two_pi_div_three:
    def __init__(self):
        self.rule = "cos(2*pi/3)=-1/2"
        self.no_mapping = True
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        return ["rw cos_two_pi_div_three"]

class cos_three_pi_div_four:
    def __init__(self):
        self.rule = "cos(3*pi/4)=-sqrt(2)/2"
        self.no_mapping = True
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        return ["rw cos_three_pi_div_four"]

class cos_five_pi_div_six:
    def __init__(self):
        self.rule = "cos(5*pi/6)=-sqrt(3)/2"
        self.no_mapping = True
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        return ["rw cos_five_pi_div_six"]

class cos_pi:
    def __init__(self):
        self.rule = "cos(pi)=-1"
        self.no_mapping = True
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        return ["rw cos_pi"]

class cos_pi_div_twelve:
    def __init__(self):
        self.rule = "cos(pi/12)=sqrt(2)/4+sqrt(6)/4"
        self.no_mapping = True
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        return ["rw cos_pi_div_twelve"]

class cos_pi_div_two:
    def __init__(self):
        self.rule = "cos(pi/2)=0"
        self.no_mapping = True
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        return ["rw cos_pi_div_two"]

class cos_pi_div_three:
    def __init__(self):
        self.rule = "cos(pi/3)=1/2"
        self.no_mapping = True
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        return ["rw cos_pi_div_three"]

class cos_pi_div_four:
    def __init__(self):
        self.rule = "cos(pi/4)=sqrt(2)/2"
        self.no_mapping = True
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        return ["rw cos_pi_div_four"]

class cos_pi_div_six:
    def __init__(self):
        self.rule = "cos(pi/6)=sqrt(3)/2"
        self.no_mapping = True
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        return ["rw cos_pi_div_six"]

class tan_zero:
    def __init__(self):
        self.rule = "tan(0)=0"
        self.no_mapping = True
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        return ["rw tan_zero"]

class tan_pi:
    def __init__(self):
        self.rule = "tan(pi)=0"
        self.no_mapping = True
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        return ["rw tan_pi"]

class tan_two_pi_div_three:
    def __init__(self):
        self.rule = "tan(2*pi/3)=-sqrt(3)"
        self.no_mapping = True
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        return ["rw tan_two_pi_div_three"]

class tan_three_pi_div_four:
    def __init__(self):
        self.rule = "tan(3*pi/4)=-1"
        self.no_mapping = True
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        return ["rw tan_three_pi_div_four"]

class tan_pi_div_twelve:
    def __init__(self):
        self.rule = "tan(pi/12)=2-sqrt(3)"
        self.no_mapping = True
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        return ["rw tan_pi_div_twelve"]

class tan_pi_div_three:
    def __init__(self):
        self.rule = "tan(pi/3)=sqrt(3)"
        self.no_mapping = True
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        return ["rw tan_pi_div_three"]

class tan_pi_div_four:
    def __init__(self):
        self.rule = "tan(pi/4)=1"
        self.no_mapping = True
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        return ["rw tan_pi_div_four"]

class tan_pi_div_six:
    def __init__(self):
        self.rule = "tan(pi/6)=sqrt(3)/3"
        self.no_mapping = True
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        return ["rw tan_pi_div_six"]

#special angle end


# angle switch begin

''' neg '''
class sin_neg:
    def __init__(self):
        self.rule = "sin(X)=-sin(2*pi*K - X)"
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        _k, _x = mapping[K], mapping[X]
        # have_goal = f"have : sin({_x}) = -sin(-({_x}) + ({_k} : ℤ) * (2*pi))"
        steps = [
                    # have_goal,
                    f'rw sin_eq_neg_sin_neg_add_int_mul_two_pi ({_x}) ({_k})',
                ] + common_calc_steps
        return steps

class cos_neg:
    def __init__(self):
        self.rule = "cos(X)=cos(2*pi*K - X)"
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        _k, _x = mapping[K], mapping[X]
        # have_goal = f"have : cos({_x}) = cos(-({_x}) + ({_k} : ℤ) * (2*pi))"
        steps = [
                    # have_goal,
                    f'rw cos_eq_cos_neg_add_int_mul_two_pi ({_x}) ({_k})',
                ] + common_calc_steps
        return steps

class tan_neg:
    def __init__(self):
        self.rule = "tan(X)=-tan(pi*K - X)"
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        _k, _x = mapping[K], mapping[X]
        # have_goal = f"have : tan({_x}) = -tan(-({_x}) + ({_k} : ℤ) * pi)"
        steps = [
                    # have_goal,
                    f'rw tan_eq_neg_tan_neg_add_int_mul_pi ({_x}) ({_k})',
                ] + common_calc_steps
        return steps

''' 2 pi period '''
class sin_add_int_mul_two_pi:
    def __init__(self):
        self.rule = "sin(X)=sin(2*pi*K + X)"
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        _k, _x = mapping[K], mapping[X]
        # have_goal = f"have : sin ({_x}) = sin({_x} + ({_k} : ℤ) * (2*pi))"
        steps = [
                    # have_goal,
                    f'rw sin_eq_sin_add_int_mul_two_pi ({_x}) ({_k})',
                ] + common_calc_steps
        return steps

class cos_add_int_mul_two_pi:
    def __init__(self):
        self.rule = "cos(X)=cos(2*pi*K + X)"
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        _k, _x = mapping[K], mapping[X]
        # have_goal = f"have : cos ({_x}) = cos({_x} + ({_k} : ℤ) * (2*pi))"
        steps = [
                    # have_goal,
                    f'rw cos_eq_cos_add_int_mul_two_pi ({_x}) ({_k})',
                ] + common_calc_steps
        return steps

''' pi period'''
class sin_add_int_mul_two_pi_add_pi:
    def __init__(self):
        self.rule = "sin(X)=-sin(X + pi*(2*K + 1))"
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        _k, _x = mapping[K], mapping[X]
        # have_goal = f"have : sin ({_x}) = -sin({_x} + ({_k} : ℤ) * (2*pi) + pi)"
        steps = [
                    # have_goal,
                    f'rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi ({_x}) ({_k})',
                ] + common_calc_steps
        return steps

class cos_add_int_mul_two_pi_add_pi:
    def __init__(self):
        self.rule = "cos(X)=-cos(X + pi*(2*K + 1))"
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        _k, _x = mapping[K], mapping[X]
        # have_goal = f"have : cos ({_x}) = -cos({_x} + ({_k} : ℤ) * (2*pi) + pi)"
        steps = [
                    # have_goal,
                    f'rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi ({_x}) ({_k})',
                ] + common_calc_steps
        return steps

class tan_add_int_mul_pi:
    def __init__(self):
        self.rule = "tan(X)=tan(pi*K + X)"
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        _k, _x = mapping[K], mapping[X]
        # have_goal = f"have : tan ({_x}) = tan({_x} + ({_k} : ℤ) * pi)"
        steps = [
                    # have_goal,
                    f'rw tan_eq_tan_add_int_mul_pi ({_x}) ({_k})',
                ] + common_calc_steps
        return steps

class sin_neg_add_int_mul_two_pi_add_pi:
    def __init__(self):
        self.rule = "sin(X)=sin(-X + pi*(2*K + 1))"
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        _k, _x = mapping[K], mapping[X]
        # have_goal = f"have : sin ({_x}) = sin(-({_x}) + ({_k} : ℤ) * (2*pi) + pi)"
        steps = [
                    # have_goal,
                    f'rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi ({_x}) ({_k})',
                ] + common_calc_steps
        return steps

class cos_neg_add_int_mul_two_pi_add_pi:
    def __init__(self):
        self.rule = "cos(X)=-cos(-X + pi*(2*K + 1))"
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        _k, _x = mapping[K], mapping[X]
        # have_goal = f"have : cos ({_x}) = -cos(-({_x}) + ({_k} : ℤ) * (2*pi) + pi)"
        steps = [
                    # have_goal,
                    f'rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi ({_x}) ({_k})',
                ] + common_calc_steps
        return steps

'''pi/2 period'''
class sin_add_pi_div_two:
    def __init__(self):
        self.rule = "sin(X)=-cos(2*pi*K + X + pi/2)"
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        _k, _x = mapping[K], mapping[X]
        # have_goal = f"have : sin ({_x}) = -cos({_x} + pi/2 + ({_k} : ℤ) * (2*pi))"
        steps = [
                    # have_goal,
                    f'rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi ({_x}) ({_k})',
                ] + common_calc_steps
        return steps

class sin_add_pi_div_two_add_pi:
    def __init__(self):
        self.rule = "sin(X)=cos(X + pi*(2*K + 1) + pi/2)"
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        _k, _x = mapping[K], mapping[X]
        # have_goal = f"have : sin ({_x}) = cos({_x} + pi/2 + ({_k} : ℤ) * (2*pi) + pi)"
        steps = [
                    # have_goal,
                    f'rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi ({_x}) ({_k})',
                ] + common_calc_steps
        return steps

class sin_neg_add_pi_div_two_add_pi:
    def __init__(self):
        self.rule = "sin(X)=-cos(-X + pi*(2*K + 1) + pi/2)"
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        _k, _x = mapping[K], mapping[X]
        # have_goal = f"have : sin ({_x}) = -cos(-({_x}) + pi/2 + ({_k} : ℤ) * (2*pi) + pi)"
        steps = [
                    # have_goal,
                    f'rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi ({_x}) ({_k})',
                ] + common_calc_steps
        return steps

class cos_add_pi_div_two:
    def __init__(self):
        self.rule = "cos(X)=sin(2*pi*K + X + pi/2)"
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        _k, _x = mapping[K], mapping[X]
        # have_goal = f"have : cos ({_x}) = sin({_x} + pi/2 + ({_k} : ℤ) * (2*pi))"
        steps = [
                    # have_goal,
                    f'rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi ({_x}) ({_k})',
                ] + common_calc_steps
        return steps

class cos_add_pi_div_two_add_pi:
    def __init__(self):
        self.rule = "cos(X)=-sin(X + pi*(2*K + 1) + pi/2)"
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        _k, _x = mapping[K], mapping[X]
        # have_goal = f"have : cos ({_x}) = -sin({_x} + pi/2 + ({_k} : ℤ) * (2*pi) + pi)"
        steps = [
                    # have_goal,
                    f'rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi ({_x}) ({_k})',
                ] + common_calc_steps
        return steps

class cos_neg_add_pi_div_two_add_pi:
    def __init__(self):
        self.rule = "cos(X)=-sin(-X + pi*(2*K + 1) + pi/2)"
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        _k, _x = mapping[K], mapping[X]
        # have_goal = f"have : cos ({_x}) = -sin(-({_x}) + pi/2 + ({_k} : ℤ) * (2*pi) + pi)"
        steps = [
                    # have_goal,
                    f'rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi ({_x}) ({_k})',
                ] + common_calc_steps
        return steps

class tan_add_pi_div_two:
    def __init__(self):
        self.rule = "tan(X)=-1/tan(pi*K + X + pi/2)"
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        _k, _x = mapping[K], mapping[X]
        # have_goal = f"have : tan ({_x}) = -1/tan({_x} + pi/2 + ({_k} : ℤ) * pi)"
        steps = [
                    # have_goal,
                    f'rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi ({_x}) ({_k})',
                ] + common_calc_steps
        return steps

class sin_neg_add_pi_div_two:
    def __init__(self):
        self.rule = "sin(X)=cos(2*pi*K - X + pi/2)"
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        _k, _x = mapping[K], mapping[X]
        # have_goal = f"have : sin ({_x}) = cos(-({_x}) + pi/2 + ({_k} : ℤ) * (2*pi))"
        steps = [
                    # have_goal,
                    f'rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi ({_x}) ({_k})',
                ] + common_calc_steps
        return steps

class cos_neg_add_pi_div_two:
    def __init__(self):
        self.rule = "cos(X)=sin(2*pi*K - X + pi/2)"
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        _k, _x = mapping[K], mapping[X]
        # have_goal = f"have : cos ({_x}) = sin(-({_x}) + pi/2 + ({_k} : ℤ) * (2*pi))"
        steps = [
                    # have_goal,
                    f'rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi ({_x}) ({_k})',
                ] + common_calc_steps
        return steps

class tan_neg_add_pi_div_two:
    def __init__(self):
        self.rule = "tan(X)=1/tan(pi*K - X + pi/2)"
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        _k, _x = mapping[K], mapping[X]
        # have_goal = f"have : tan ({_x}) = 1/tan(-({_x}) + pi/2 + ({_k} : ℤ) * pi)"
        steps = [
                    # have_goal,
                    f'rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi ({_x}) ({_k})',
                ] + common_calc_steps
        return steps

# angle switch end


# multiple angles begin

congrarg_linarith = [
    "{",
    "apply congr_arg",
    "ring",
    "},",
]

class sin_two_mul:
    def __init__(self):
        self.rule = "sin(2*X)=2*sin(X)*cos(X)"
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        _x = mapping[X]
        have_goal = f"have : sin ({2*_x}) = sin(2*({_x}))"
        steps = [
                    have_goal,
                ] + congrarg_linarith + \
                [   "rw this",
                    "rw sin_two_mul",
                    "try {ring}"
                ]
        return steps

class sin_three_mul:
    def __init__(self):
        self.rule = "sin(3*X)=-4*sin(X)**3 + 3*sin(X)"
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        _x = mapping[X]
        have_goal = f"have : sin ({3*_x}) = sin(3*({_x}))"
        steps = [
                    have_goal,
                ] + congrarg_linarith + \
                [   "rw this",
                    "rw sin_three_mul",
                    "try {ring}"
                ]
        return steps

class cos_two_mul_1:
    def __init__(self):
        self.rule = "cos(2*X)=2*cos(X)**2 - 1"
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        _x = mapping[X]
        have_goal = f"have : cos ({2*_x}) = cos(2*({_x}))"
        steps = [
                    have_goal,
                ] + congrarg_linarith + \
                [   "rw this",
                    "rw cos_two_mul",
                    "try {ring}"
                ]
        return steps

class cos_two_mul_2:
    def __init__(self):
        self.rule = "cos(2*X)=-sin(X)**2 + cos(X)**2"
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        _x = mapping[X]
        have_goal = f"have : cos ({2*_x}) = cos(2*({_x}))"
        steps = [
                    have_goal,
                ] + congrarg_linarith + \
                [   "rw this",
                    "rw cos_two_mul'",
                    "try {ring}"
                ]
        return steps

class cos_two_mul_3:
    def __init__(self):
        self.rule = "cos(2*X)=1 - 2*sin(X)**2"
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        _x = mapping[X]
        have_goal = f"have : cos ({2*_x}) = cos(2*({_x}))"
        steps = [
                    have_goal,
                ] + congrarg_linarith + \
                [   "rw this",
                    "rw cos_two_mul''",
                    "try {ring}"
                ]
        return steps

class cos_three_mul:
    def __init__(self):
        self.rule = "cos(3*X)=4*cos(X)**3 - 3*cos(X)"
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        _x = mapping[X]
        have_goal = f"have : cos ({3*_x}) = cos(3*({_x}))"
        steps = [
                    have_goal,
                ] + congrarg_linarith + \
                [   "rw this",
                    "rw cos_three_mul",
                    "try {ring}"
                ]
        return steps

class tan_two_mul:
    def __init__(self):
        self.rule = "tan(2*X)=2*tan(X)/(1 - tan(X)**2)"
        self.has_nonzero = True

    def get_tactics(self, mapping, left, right):
        _x = mapping[X]
        have_goal = f"have : tan ({2*_x}) = tan(2*({_x}))"
        steps = [
                    have_goal,
                ] + congrarg_linarith + \
                [   "rw this",
                    "rw tan_two_mul",
                    "repeat {assumption}"
                ]
        return steps

    def get_nonzero(self, mapping, left, right):
        _x = mapping[X]
        return [f"cos({_x})"]

class sin_sq_cos_two_mul:
    def __init__(self):
        self.rule = "sin(X)**2=1/2 - cos(2*X)/2"
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        _x = mapping[X]
        have_goal = f"have : cos ({2*_x}) = cos(2*({_x}))"
        steps = [
                    have_goal,
                ] + congrarg_linarith + \
                [   "rw this",
                    "rw cos_two_mul''",
                    "try {ring}"
                ]
        return steps

class cos_sq_cos_two_mul:
    def __init__(self):
        self.rule = "cos(X)**2=cos(2*X)/2 + 1/2"
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        _x = mapping[X]
        have_goal = f"have : cos ({2*_x}) = cos(2*({_x}))"
        steps = [
                    have_goal,
                ] + congrarg_linarith + \
                [   "rw this",
                    "rw cos_two_mul",
                    "try {ring}"
                ]
        return steps

class cos_eq_sin_two_mul:
    def __init__(self):
        self.rule = "cos(X)=sin(2*X)/(2*sin(X))"
        self.need_rule = True
        self.has_nonzero = True

    def get_tactics(self, mapping, left, right):
        _x = mapping[X]
        # simp_ignore = get_simp_ignore(left, right)
        have_goal = f"have : sin ({2*_x}) = sin(2*({_x}))"
        steps = [
                    have_goal,
                ] + congrarg_linarith + \
                [   "rw this",
                    "rw sin_two_mul",
                    # "try {field_simp " + simp_ignore + "}",
                    # "try {simp at *}",
                    #"try {field_simp at *}",
                    "try {field_simp at *}",
                    "try {ring}"
                ]
        return steps

    def get_nonzero(self, mapping, left, right):
        _x = mapping[X]
        return [f"sin({_x})"]

class sin_eq_sin_two_mul:
    def __init__(self):
        self.rule = "sin(X)=sin(2*X)/(2*cos(X))"
        self.need_rule = True
        self.has_nonzero = True

    def get_tactics(self, mapping, left, right):
        _x = mapping[X]
        # simp_ignore = get_simp_ignore(left, right)
        have_goal = f"have : sin ({2*_x}) = sin(2*({_x}))"
        steps = [
                    have_goal,
                ] + congrarg_linarith + \
                [   "rw this",
                    "rw sin_two_mul",
                    # "try {field_simp " + simp_ignore + "}",
                    # "try {simp at *}",
                    "try {field_simp at *}",
                    #"try {field_simp}",
                    "try {ring}",
                    "repeat {assumption}",
                ]
        return steps

    def get_nonzero(self, mapping, left, right):
        _x = mapping[X]
        return [f"cos({_x})"]

# multiple angles end

# sum_to_mul
# for
# common_prove_have_step = [
#     "apply congr_arg",
#     "ring",
#     "rw this"
# ]

class sin_add_sin:
    def __init__(self):
        self.rule = "sin(X) + sin(Y)=2*sin(X/2 + Y/2)*cos(X/2 - Y/2)"
        self.need_rule = True
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        _x, _y = mapping[X], mapping[Y]
        _x_str, _y_str = str(_x).replace(" ", ""), str(_y).replace(" ", "")
        left = left.replace(" ", "")
        x_pos = left.index(f"sin({_x_str})")
        y_pos = left.index(f"sin({_y_str})")
        steps = ["rw add_comm"] if y_pos < x_pos else []
        steps.append("rw sin_add_sin")
        steps += [
            f"have : sin((({_x}) + ({_y}))/2) = sin ({(_x + _y)/2})",
        ] + congrarg_linarith + ["rw this", ]
        steps += [
            f"have : cos((({_x}) - ({_y}))/2) = cos({(_x - _y)/2})"
        ] + congrarg_linarith + ["rw this", ] + ["try {ring}"]
        return steps

class sin_sub_sin:
    def __init__(self):
        self.rule = "sin(X) - sin(Y)=2*sin(X/2 - Y/2)*cos(X/2 + Y/2)"
        self.need_rule = True
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        _x, _y = mapping[X], mapping[Y]
        _x_str, _y_str = str(_x).replace(" ", ""), str(_y).replace(" ", "")
        left = left.replace(" ", "")
        x_pos = left.index(f"sin({_x_str})")
        y_pos = left.index(f"sin({_y_str})")
        steps = ["rw neg_add_eq_sub"] if y_pos < x_pos else [] #-sin(Y) + sin(X) = sin(X) - sin(Y)
        steps.append("rw sin_sub_sin")
        steps += [
            f"have : cos((({_x}) + ({_y}))/2) = cos ({(_x + _y)/2})",
        ] + congrarg_linarith + ["rw this", ]
        steps += [
            f"have : sin((({_x}) - ({_y}))/2) = sin({(_x - _y)/2})"
        ] + congrarg_linarith + ["rw this", ] + ["try {ring}"]
        return steps

class cos_add_cos:
    def __init__(self):
        self.rule = "cos(X) + cos(Y)=2*cos(X/2 - Y/2)*cos(X/2 + Y/2)"
        self.need_rule = True
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        _x, _y = mapping[X], mapping[Y]
        _x_str, _y_str = str(_x).replace(" ", ""), str(_y).replace(" ", "")
        left = left.replace(" ", "")
        x_pos = left.index(f"cos({_x_str})")
        y_pos = left.index(f"cos({_y_str})")
        steps = ["rw add_comm"] if y_pos < x_pos else []
        steps.append("rw cos_add_cos")
        steps += [
            f"have : cos((({_x}) + ({_y}))/2) = cos ({(_x + _y)/2})",
        ] + congrarg_linarith + ["rw this", ]
        steps += [
            f"have : cos((({_x}) - ({_y}))/2) = cos({(_x - _y)/2})"
        ] + congrarg_linarith + ["rw this", ] + ["try {ring}"]
        return steps

class cos_sub_cos:
    def __init__(self):
        self.rule = "cos(X) - cos(Y)=-2*sin(X/2 - Y/2)*sin(X/2 + Y/2)"
        self.need_rule = True
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        _x, _y = mapping[X], mapping[Y]
        _x_str, _y_str = str(_x).replace(" ", ""), str(_y).replace(" ", "")
        left = left.replace(" ", "")
        x_pos = left.index(f"cos({_x_str})")
        y_pos = left.index(f"cos({_y_str})")
        steps = ["rw neg_add_eq_sub"] if y_pos < x_pos else []
        steps.append("rw cos_sub_cos")
        steps += [
            f"have : sin((({_x}) + ({_y}))/2) = sin ({(_x + _y)/2})",
        ] + congrarg_linarith + ["rw this", ]
        steps += [
            f"have : sin((({_x}) - ({_y}))/2) = sin({(_x - _y)/2})"
        ] + congrarg_linarith + ["rw this", ] + ["try {ring}"]
        return steps

#todo: tan denom
class tan_add_tan:
    def __init__(self):
        self.rule = "tan(X) + tan(Y)=(-tan(X)*tan(Y) + 1)*tan(X + Y)"
        self.need_rule = True
        self.has_nonzero = True

    def get_tactics(self, mapping, left, right):
        _x, _y = mapping[X], mapping[Y]
        _x_str, _y_str = str(_x).replace(" ", ""), str(_y).replace(" ", "")
        left = left.replace(" ", "")
        x_pos = left.index(f"tan({_x_str})")
        y_pos = left.index(f"tan({_y_str})")
        steps = ["rw add_comm"] if y_pos < x_pos else []
        steps.append("rw tan_add_tan")
        #steps.append("repeat {assumption}")
        steps += [
            f"have : tan(({_x}) + ({_y})) = tan ({_x + _y})",
        ] + congrarg_linarith + ["rw this", ] + ["try {ring}", "repeat {assumption}"]  # repeat {finish}
        return steps

    def get_nonzero(self, mapping, left, right):
        _x, _y = mapping[X], mapping[Y]
        return [f"cos({_x})", f"cos({_y})", f"1 - tan({_x}) * tan({_y})"]

class tan_sub_tan:
    def __init__(self):
        self.rule = "tan(X) - tan(Y)=(tan(X)*tan(Y) + 1)*tan(X - Y)"
        self.need_rule = True
        self.has_nonzero = True

    def get_tactics(self, mapping, left, right):
        _x, _y = mapping[X], mapping[Y]
        _x_str, _y_str = str(_x).replace(" ", ""), str(_y).replace(" ", "")
        left = left.replace(" ", "")
        x_pos = left.index(f"tan({_x_str})")
        y_pos = left.index(f"tan({_y_str})")
        steps = ["rw neg_add_eq_sub"] if y_pos < x_pos else []
        steps.append("rw tan_sub_tan")
        #steps.append("repeat {assumption}")
        steps += [
            f"have : tan(({_x}) - ({_y})) = tan ({_x - _y})",
        ] + congrarg_linarith + ["rw this", ] + ["try {ring}", "repeat {assumption}"]
        return steps

    def get_nonzero(self, mapping, left, right):
        _x, _y = mapping[X], mapping[Y]
        return [f"cos({_x})", f"cos({_y})", f"1 + tan({_x}) * tan({_y})"]

class tan_sub_tan_2:
    def __init__(self):
        self.rule = "tan(X) - tan(Y)=sin(X - Y)/(cos(X)*cos(Y))"
        self.need_rule = True
        self.has_nonzero = True

    def get_tactics(self, mapping, left, right):
        _x, _y = mapping[X], mapping[Y]
        _x_str, _y_str = str(_x).replace(" ", ""), str(_y).replace(" ", "")
        left = left.replace(" ", "")
        x_pos = left.index(f"tan({_x_str})")
        y_pos = left.index(f"tan({_y_str})")
        steps = ["rw neg_add_eq_sub"] if y_pos < x_pos else []
        steps.append("rw tan_sub_tan'")
        if _x_str in ["x", "y"] and _y_str in ["x", "y"] and y_pos>= x_pos:
            steps += [ "repeat {assumption}"]
        else:
            
            steps += [
                f"have : sin(({_x}) - ({_y})) = sin ({_x - _y})",
            ] + congrarg_linarith + ["rw this", ] + ["try {field_simp}", "try {left}", "try {ring}", "repeat {assumption}"]
        return steps

    def get_nonzero(self, mapping, left, right):
        _x, _y = mapping[X], mapping[Y]
        return [f"cos({_x})", f"cos({_y})"]

class tan_div_two_1:
    def __init__(self):
        self.rule = "tan(X/2)=(1 - cos(X))/sin(X)"
        self.has_nonzero = True

    def get_tactics(self, mapping, left, right):
        _x = mapping[X]
        #have_goal = f"have : cos({_x/2}) = cos(({_x})/2)"
        steps = []#[have_goal] + congrarg_linarith + ["rw this at *"] #for cos (x/2) ≠ 0
        have_goal = f"have : tan({_x/2}) = tan(({_x})/2)"
        steps += [have_goal] + \
                 congrarg_linarith + \
                 ["rw this",
                  "rw tan_div_two",
                  "repeat {assumption}"]#"tidy"]
        return steps

    def get_nonzero(self, mapping, left, right):
        _x = mapping[X]
        return [f"cos(({_x})/2)"]

class tan_div_two_2:
    def __init__(self):
        self.rule = "tan(X/2)=sin(X)/(1+ cos(X))"
        self.has_nonzero = True

    def get_tactics(self, mapping, left, right):
        _x = mapping[X]
        #have_goal = f"have : cos({_x/2}) = cos(({_x})/2)"
        steps = []#[have_goal] + congrarg_linarith + ["rw this at *"] #for cos (x/2) ≠ 0
        have_goal = f"have : tan({_x/2}) = tan(({_x})/2)"
        steps += [have_goal] + \
                 congrarg_linarith + \
                 ["rw this",
                  "rw tan_div_two'",
                  "repeat {assumption}"]
        return steps

    def get_nonzero(self, mapping, left, right):
        _x = mapping[X]
        return [f"cos(({_x})/2)"]
        #return [f"cos ({_x/2})"]

#mul_to_sum
class sin_mul_sin:
    def __init__(self):
        self.rule = "sin(X)*sin(Y)=cos(X - Y)/2 - cos(X + Y)/2"
        self.need_rule = True
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        _x, _y = mapping[X], mapping[Y]
        _x_str, _y_str = str(_x).replace(" ", ""), str(_y).replace(" ", "")
        left = left.replace(" ", "")
        x_pos = left.index(f"sin({_x_str})")
        y_pos = left.index(f"sin({_y_str})")
        steps = ["rw mul_comm"] if y_pos < x_pos else []
        steps.append("rw sin_mul_sin")
        steps += [
            f"have : cos(({_x}) + ({_y})) = cos ({_x + _y})",
        ] + congrarg_linarith + ["rw this", ]
        steps += [
            f"have : cos(({_x}) - ({_y})) = cos ({_x - _y})",
        ] + congrarg_linarith + ["rw this", ] + ["try {ring}"]
        return steps

class sin_mul_cos:
    def __init__(self):
        self.rule = "sin(X)*cos(Y)=sin(X - Y)/2 + sin(X + Y)/2"
        self.need_rule = True
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        _x, _y = mapping[X], mapping[Y]
        _x_str, _y_str = str(_x).replace(" ", ""), str(_y).replace(" ", "")
        print("_y_str:{}".format(_y_str))
        print("left:{}".format(left))

        left = left.replace(" ", "")
        x_pos = left.index(f"sin({_x_str})")
        y_pos = left.index(f"cos({_y_str})")
        steps = ["rw mul_comm"] if y_pos < x_pos else []
        steps.append("rw sin_mul_cos")
        steps += [
            f"have : sin(({_x}) + ({_y})) = sin ({_x + _y})",
        ] + congrarg_linarith + ["rw this", ]
        steps += [
            f"have : sin(({_x}) - ({_y})) = sin ({_x - _y})",
        ] + congrarg_linarith + ["rw this", ] + ["try {ring}"]
        return steps

class cos_mul_sin:
    def __init__(self):
        self.rule = "sin(Y)*cos(X)=-sin(X - Y)/2 + sin(X + Y)/2"
        self.need_rule = True
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        _x, _y = mapping[X], mapping[Y]
        _x_str, _y_str = str(_x).replace(" ", ""), str(_y).replace(" ", "")
        left = left.replace(" ", "")
        x_pos = left.index(f"cos({_x_str})")
        y_pos = left.index(f"sin({_y_str})")
        steps = ["rw mul_comm"] if y_pos < x_pos else []
        steps.append("rw cos_mul_sin")
        steps += [
            f"have : sin(({_x}) + ({_y})) = sin ({_x + _y})",
        ] + congrarg_linarith + ["rw this", ]
        steps += [
            f"have : sin(({_x}) - ({_y})) = sin ({_x - _y})",
        ] + congrarg_linarith + ["rw this", ] + ["try {ring}"]
        return steps

class cos_mul_cos:
    def __init__(self):
        self.rule = "cos(X)*cos(Y)=cos(X - Y)/2 + cos(X + Y)/2"
        self.need_rule = True
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        _x, _y = mapping[X], mapping[Y]
        _x_str, _y_str = str(_x).replace(" ", ""), str(_y).replace(" ", "")
        left = left.replace(" ", "")
        x_pos = left.index(f"cos({_x_str})")
        y_pos = left.index(f"cos({_y_str})")

        steps = ["rw mul_comm"] if y_pos < x_pos else []
        steps.append("rw cos_mul_cos")
        steps += [
            f"have : cos(({_x}) + ({_y})) = cos ({_x + _y})",
        ] + congrarg_linarith + ["rw this", ]
        steps += [
            f"have : cos(({_x}) - ({_y})) = cos ({_x - _y})",
        ] + congrarg_linarith + ["rw this", ] + ["try {ring}"]
        return steps

class tan_mul_tan:
    def __init__(self):
        self.rule = "tan(X)*tan(Y)=(tan(X) - tan(Y))/tan(X - Y) - 1"
        self.need_rule = True
        self.has_nonzero = True

    def get_tactics(self, mapping, left, right):
        _x, _y = mapping[X], mapping[Y]
        _x_str, _y_str = str(_x).replace(" ", ""), str(_y).replace(" ", "")
        left = left.replace(" ", "")
        x_pos = left.index(f"tan({_x_str})")
        y_pos = left.index(f"tan({_y_str})")
        steps = ["rw mul_comm"] if y_pos < x_pos else []
        steps.append("rw tan_mul_tan")
        #steps.append("repeat {assumption}")'
       # if "x" in _x
        steps += [
            f"have : tan(({_x}) - ({_y})) = tan ({_x - _y})",
        ] + congrarg_linarith + ["rw this", "try {field_simp}", "try {left}", "try {ring}", "repeat {assumption}"]
        return steps

    def get_nonzero(self, mapping, left, right):
        _x, _y = mapping[X], mapping[Y]
        return [f"cos({_x})", f"cos({_y})", f"tan(({_x})-({_y}))", f"1+tan({_x})*tan({_y})"]

class tan_mul_tan_2:
    def __init__(self):
        self.rule = "tan(X)*tan(Y)=-(tan(X) + tan(Y))/tan(X + Y) + 1"
        self.need_rule = True
        self.has_nonzero = True

    def get_tactics(self, mapping, left, right):
        _x, _y = mapping[X], mapping[Y]
        _x_str, _y_str = str(_x).replace(" ", ""), str(_y).replace(" ", "")
        left = left.replace(" ", "")
        x_pos = left.index(f"tan({_x_str})")
        y_pos = left.index(f"tan({_y_str})")
        steps = ["rw mul_comm"] if y_pos < x_pos else []
        steps.append("rw tan_mul_tan'")
        #steps.append()
        steps += [
            f"have : tan(({_x}) + ({_y})) = tan ({_x + _y})",
        ] + congrarg_linarith + ["rw this", "try {field_simp}", "try {left}", "try {ring}", "repeat {assumption}"]
        return steps

    def get_nonzero(self, mapping, left, right):
        _x, _y = mapping[X], mapping[Y]
        return [f"cos({_x})", f"cos({_y})", f"tan(({_x})+({_y}))", f"1-tan({_x})*tan({_y})"]

#add_diff angle
class sin_add:
    def __init__(self):
        self.rule = "sin(X + Y)=sin(X)*cos(Y) + sin(Y)*cos(X)"
        self.need_rule = True
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        _x, _y = mapping[X], mapping[Y]
        steps = [f"have : {left} = sin(({_x}) + ({_y}))"]
        steps += congrarg_linarith + ["rw this", ] + [
            "rw sin_add",
            "try {ring}"
        ]

        return steps

class sin_sub:
    def __init__(self):
        self.rule = "sin(X - Y)=sin(X)*cos(Y) - sin(Y)*cos(X)"
        self.need_rule = True
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        _x, _y = mapping[X], mapping[Y]
        steps = [f"have : {left} = sin(({_x}) - ({_y}))"]
        steps += congrarg_linarith + ["rw this", ] + [
            "rw sin_sub",
            "try {ring}"
        ]

        return steps

class cos_add:
    def __init__(self):
        self.rule = "cos(X + Y)=-sin(X)*sin(Y) + cos(X)*cos(Y)"
        self.need_rule = True
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        _x, _y = mapping[X], mapping[Y]
        steps = [f"have : {left} = cos(({_x}) + ({_y}))"]
        steps += congrarg_linarith + ["rw this", ] + [
            "rw cos_add",
            "try {ring}"
        ]

        return steps

class cos_sub:
    def __init__(self):
        self.rule = "cos(X - Y)=sin(X)*sin(Y) + cos(X)*cos(Y)"
        self.need_rule = True
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        _x, _y = mapping[X], mapping[Y]
        steps = [f"have : {left} = cos(({_x}) - ({_y}))"]
        steps += congrarg_linarith + ["rw this", ] + [
            "rw cos_sub",
            "try {ring}"
        ]

        return steps

class tan_add:
    def __init__(self):
        self.rule = "tan(X + Y)=(tan(X) + tan(Y))/(-tan(X)*tan(Y) + 1)"
        self.need_rule = True
        self.has_nonzero = True

    def get_tactics(self, mapping, left, right):
        _x, _y = mapping[X], mapping[Y]
        steps = [f"have : tan({_x+_y}) = tan(({_x}) + ({_y}))"]
        steps += congrarg_linarith + ["rw this", ] + [
            "rw tan_add",
            
            "try {field_simp}",
            "try {ring_exp}",
            "repeat {assumption}"
            #"repeat {finish}",
        ]

        return steps

    def get_nonzero(self, mapping, left, right):
        _x, _y = mapping[X], mapping[Y]
        return [f"cos({_x})", f"cos({_y})"]

class tan_sub:
    def __init__(self):
        self.rule = "tan(X - Y)=(tan(X) - tan(Y))/(1 + tan(X)*tan(Y))"
        self.need_rule = True
        self.has_nonzero = True

    def get_tactics(self, mapping, left, right):
        _x, _y = mapping[X], mapping[Y]
        steps = [f"have : tan({_x - _y}) = tan(({_x}) - ({_y}))"]
        steps += congrarg_linarith + ["rw this", ] + [
            "rw tan_sub",
            "try {field_simp}",
            "try {left}",
            "try {ring_exp}",
            "repeat {assumption}"
        ]

        return steps

    def get_nonzero(self, mapping, left, right):
        _x, _y = mapping[X], mapping[Y]
        return [f"cos({_x})", f"cos({_y})"]


#Abs
class abs_pos:
    def __init__(self):
        self.rule = "Abs(X)=X"
        self.no_mapping = True
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        return ['rw abs_eq_self.mpr ᾰ',
                'try {ring}',]


class abs_neg:
    def __init__(self):
        self.rule = "Abs(X)=-X"
        self.no_mapping = True
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        return ['rw abs_eq_neg_self.mpr ᾰ',
                'try {ring}',]

#others
class tan_eq_sin_div_cos:
    def __init__(self):
        self.rule = "tan(X)=sin(X)/cos(X)"
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        _x = mapping[X]
        steps = ["rw tan_eq_sin_div_cos"]
        return steps

class sin_div_cos_eq_tan:
    def __init__(self):
        self.rule = "sin(X)/cos(X)=tan(X)"
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        _x = mapping[X]
        steps = ["rw tan_eq_sin_div_cos"]
        return steps

class sin_sq_add_cos_sq:
    def __init__(self):
        self.rule = "sin(X)**2 + cos(X)**2=1"
        self.need_rule = True
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        _x = mapping[X]
        sin_pos = left.index("sin")
        cos_pos = left.index("cos")
        if cos_pos < sin_pos:
            steps = ["rw add_comm","rw sin_sq_add_cos_sq"]
        else:
            steps = ["rw sin_sq_add_cos_sq"]
        return steps

class sin_sq:
    def __init__(self):
        self.rule = "sin(X)**2 = 1 - cos(X)**2"
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        _x = mapping[X]
        steps = ["rw sin_sq"]
        return steps

class cos_sq:
    def __init__(self):
        self.rule = "cos(X)**2 = 1 - sin(X)**2"
        self.has_nonzero = False

    def get_tactics(self, mapping, left, right):
        _x = mapping[X]
        steps = ["rw cos_sq'"]
        return steps

tactic_converter_list = [
    sin_add_int_mul_two_pi(),
    cos_add_int_mul_two_pi(),
    sin_add_int_mul_two_pi_add_pi(),
    cos_add_int_mul_two_pi_add_pi(),
    tan_add_int_mul_pi(),
    sin_add_pi_div_two(),
    cos_add_pi_div_two(),
    tan_add_pi_div_two(),
    sin_add_pi_div_two_add_pi(),
    cos_add_pi_div_two_add_pi(),
    sin_neg(),
    cos_neg(),
    tan_neg(),
    sin_neg_add_int_mul_two_pi_add_pi(),
    cos_neg_add_int_mul_two_pi_add_pi(),
    sin_neg_add_pi_div_two(),
    cos_neg_add_pi_div_two(),
    tan_neg_add_pi_div_two(),
    sin_neg_add_pi_div_two_add_pi(),
    cos_neg_add_pi_div_two_add_pi(),
    #field
    field_calc(),
    replace_const(),
    #special angle
    sin_zero(),
    sin_pi(),
    sin_pi_div_two(),
    sin_pi_div_three(),
    sin_pi_div_four(),
    sin_pi_div_six(),
    sin_pi_div_twelve(),
    sin_two_pi_div_three(),
    sin_three_pi_div_four(),
    sin_five_pi_div_six(),
    cos_zero(),
    cos_pi(),
    cos_pi_div_two(),
    cos_pi_div_three(),
    cos_pi_div_four(),
    cos_pi_div_six(),
    cos_pi_div_twelve(),
    cos_two_pi_div_three(),
    cos_three_pi_div_four(),
    cos_five_pi_div_six(),
    tan_zero(),
    tan_pi(),
    tan_pi_div_three(),
    tan_pi_div_four(),
    tan_pi_div_six(),
    tan_pi_div_twelve(),
    tan_two_pi_div_three(),
    tan_three_pi_div_four(),
    sin_two_mul(),
    cos_two_mul_1(),
    cos_two_mul_2(),
    cos_two_mul_3(),
    #tan note: nonzero
    tan_two_mul(),
    tan_div_two_1(),
    tan_div_two_2(),
    cos_sq_cos_two_mul(),
    sin_sq_cos_two_mul(),
    cos_eq_sin_two_mul(),
    sin_eq_sin_two_mul(),
    sin_three_mul(),
    cos_three_mul(),
    #others
    tan_eq_sin_div_cos(),
    sin_div_cos_eq_tan(),
    sin_sq_add_cos_sq(),
    sin_sq(),
    cos_sq(),

    # #add_diff angle
    sin_add(),
    sin_sub(),
    cos_add(),
    cos_sub(),
    #tan_add(),
    tan_sub(),
    #abs
    abs_pos(),
    abs_neg(),
    # sum_to_mul
    sin_add_sin(),
    sin_sub_sin(),
    cos_add_cos(),
    cos_sub_cos(),
    tan_add_tan(),
    tan_sub_tan(),
    tan_sub_tan_2(),
    #mul_to_sum
    sin_mul_sin(),
    sin_mul_cos(),
    cos_mul_cos(),
    cos_mul_sin(),
    tan_mul_tan(),
    tan_mul_tan_2(),
]

def process_const_replacement(line):
    results = []
    patterns = ["sin \d", "sin\d", "cos \d", "cos\d", "tan \d", "tan\d", "tan pi", "tanpi", "sin pi", "sinpi", "cos pi", "cospi"]
    pattern_const = "\d+|pi"
    # pattern2 = "sin\d"

    # pattern3 = "cos \d"
    # pattern4 = "cos\d"

    # pattern5 = "tan \d"
    # pattern6 = "tan\d"
    
    for pattern in patterns:
        # print("line in:{}".format(type(line)))
        # print("pattern in:{}".format(pattern))
        results = re.findall(pattern,line)
        #print("results:{}".format(results))
        for result in results:
            const =  re.findall(pattern_const, result)[0] #pattern_const
            #print("const:{}".format(const))
            if const != None :
               result_new = result.replace(const, "(" + const +")")
               line = line.replace(result, result_new)
    
    #print("line:{}".format(line))
    return line

def strToInfix(line):

    line = process_const_replacement(line)
    print("line:{}".format(line))
    
    line = line.replace("**", "^")
    line = line.replace(' ', '')
    #    ②
    line = ''.join(line.split())
    #    ③
    #line = re.sub('s', '', line)  
    #  2) 括号统一
    line = re.sub('[{[]', '(', line)  
    line = re.sub('[}]]', ')', line)  
    
    # 2 正则匹配切分，str.split()只能按单个分隔符切分, re.split()可以接收多个分隔符
    #     pattern： []分割结果不保留分隔符，([])保留分隔符， 此处用([])
    line_split = re.split("([-, +, *, /, (, ), ^])", line)  
    # 3 分割结果包含空字符串，两种解决方法：
    #    1） 列表表达式
    infix = [x for x in line_split if x]
    #    2) filter库函数
    infix = list(filter(None,line_split))
    
    # 4 若“-”为第一位，或前一位为"("，则在前插入0
    LEN = len(infix)
    infix_temp = []
    print("=======init infix:{}".format(infix))
    for i in range(LEN):
        if infix[i] == 'sqrt' or infix[i] == '-sqrt' or infix[i] == '--sqrt':
           if infix[i+1] == '(':
              infix[i+1] = infix[i] + infix[i+1]
              continue
        elif infix[i] == '-':
            if i == 0:
                if infix[i+1] == "sin" or infix[i+1] == "cos" or infix[i+1] == "tan" or infix[i+1] == "-sin" or infix[i+1] == "-cos" or infix[i+1] == "-tan" :
                   infix_temp.append("0")
                   infix_temp.append("-")
                   infix_temp.append(infix[i+1])
                   #infix[i+1] = "-" + infix[i+1]
                   continue
                elif infix[i+1] == "(" or infix[i+1].isdigit() or infix[i+1] == "sqrt" or infix[i+1] == "-sqrt":
                   infix_temp.append("0")
                   infix_temp.append("-")
                   continue
                elif infix[i+1] == "-":
                   infix[i+2] = "-" + infix[i+2]
                   continue
                
            elif infix[i - 1] == '(' or infix[i - 1] == 'sqrt(':
                if infix[i+1] == "sin" or infix[i+1] == "cos" or infix[i+1] == "tan" or infix[i+1] == "-sin" or infix[i+1] == "-cos" or infix[i+1] == "-tan" :
                   infix_temp.append("0")
                   infix_temp.append("-")
                   #infix[i+1] = "-" + infix[i+1]
                   continue
                elif infix[i+1] == "(" or infix[i+1].isdigit() or infix[i+1] == "sqrt" or infix[i+1] == "-sqrt":
                   infix_temp.append("0")
                   infix_temp.append("-")
                   continue
                elif infix[i+1] == "-":
                   # ( - -
                   infix[i+2] = "-" + infix[i+2]
                   continue

            elif infix[i-1] in ["+" , "-", "*", "/"]:
                infix[i+1] = "-" + infix[i+1]
                continue

        infix_temp.append(infix[i])
    
    infix = infix_temp
    tokens = []
    bucket_count = 0
    sub_tokens = []
    flag = False
    print("infix:{}".format(infix))
    for i, token in enumerate(infix):
        
        if flag == True:
           sub_tokens.append(token)
           #print("sub_tokens:{}".format(sub_tokens))
           if token == "(":
              bucket_count += 1
              #print("bucket_count:{}".format(bucket_count))

        elif token != "sin" and token !="cos" and token != "tan" and token != "-sin" and token != "-cos" and token != "-tan" and token != "--sin" and token != "--cos" and token != "--tan": #and token != "sqrt" and token != "-sqrt" and token != "--sqrt":
           tokens.append(token)


        if token == ")" and flag == True:
           bucket_count -=1
           print("bucket_count:{}".format(bucket_count))
           if sub_tokens!= [] and bucket_count==0:
              print("sub_tokens in here:{}".format(sub_tokens))
              tokens.append("".join(sub_tokens))
              sub_tokens = []
              flag = False

           

        if token == "sin" or token == "cos" or token == "tan" or token == "-cos" or token == "-sin" or token == "-tan" or token == "--cos" or token == "--sin" or token == "--tan": #or token == "sqrt" or token == "-sqrt" or token == "--sqrt"   :
           sub_tokens = []
           sub_tokens.append(token)
           flag = True
        
    print("tokens:{}".format(tokens))    


    return tokens#infix



def infixToPostfix(infix):
    # 中缀表达式转后缀表达式
    stack = [] # 存储栈
    postfix = [] # 后缀表达式
    priority = {'(': 0, ')': 0, 'sqrt(':0,
                '+': 1, '-': 1,
                '*': 2, '/': 2, '^': 2}
    for i in range(len(infix)):
        char = infix[i]
        if char in priority.keys():  # 运算符号
            if stack:
                if char not in ['(', ')', 'sqrt(']:  
                    while stack and (priority[char] <= priority[stack[-1]]) and ((stack[-1] not in ['(', ')', 'sqrt('])) :     
                        temp = stack.pop()
                        if temp not in ['(', ')', 'sqrt(']:
                            postfix.append(temp)
                    stack.append(char)
                elif  char == ')':
                    
                    while stack[-1] !='(' and stack[-1] !='sqrt(':
                        temp = stack.pop()
                        postfix.append(temp)
                    bucket = stack.pop()
                    postfix.append(char)
                    postfix.append(bucket)
                else:
                    stack.append(char)
            else:
                stack.append(char)
        else:  # 数字
            postfix.append(char)
    while stack:
        temp = stack.pop()
        postfix.append(temp)
    return postfix


def Get_Denominators(strs):
    
    Infix = strToInfix(strs)
    postfix = infixToPostfix(Infix)
    #print("===================postfix:{}".format(postfix))
    stack = []
    priority = {'(': 0, ')': 0, 'sqrt(': 0,
                '+': 1, '-': 1,
                '*': 2, '/': 2, '^': 2}

    operators = priority.keys()
    denominators = []
    for token in postfix:
        if token in operators:
           if token not in ["(", ")", "/", 'sqrt(']:
              right = stack.pop()
              left = stack.pop()
              sub_formula = left + " " + token + " " + right
              stack.append(sub_formula)
           elif token == ")":
              sub_formula = stack.pop() + ")"
              stack.append(sub_formula)
           elif token == "(":
              sub_formula = "(" + stack.pop()
              stack.append(sub_formula)

           elif token == "sqrt(":
              sub_formula = "sqrt(" + stack.pop()
              stack.append(sub_formula)

           elif token == "/":
              right = stack.pop()
              left = stack.pop()
              sub_formula = left + " " + token + " " + right
              stack.append(sub_formula)
              denominator = right.replace("^", "**").replace("0 -", "-").replace("0-", "-")
              Flag = True
              if left=="0" and token=="-":
                 Flag = False
              if (not denominator.replace("**", "").replace("(", "").replace(")", "").replace("/", "").isdigit()) and (Flag==True):
                 denominators.append(denominator)
              #denominators.append(right.replace(" ^ ", "**"))

        else:
           stack.append(token)

    print("stack[-1] in Get_Denominators :{}".format(stack[-1]))
    return denominators

def formula_substitution_old(state, result, substitution_expr, expr):
    new_state = None
    new_results = []
    for substitution in result:
       if not substitution:
          continue
       new_results.append(substitution)
    
    substitution_dict = dict()
    if len(new_results)>0:
        substitution = random.choice(new_results)
        replace_variables(substitution, substitution_expr)

        for key, value in zip(substitution.keys(), substitution.values()):
            #str(list(substitution.keys())[0])
            #str(list(substitution.values())[0])
            print("key:{}".format(str(key)))
            print("value:{}".format(str(value)))
            print("substitution_expr1:{}".format(substitution_expr))
            print("type of list(substitution.values())[0]:{}".format(type(list(substitution.values())[0])))
            substitution_dict[sympify(key,evaluate = False)] = value
            key = str(key)
            value = str(value)
            if key=="X - Y":
                #111111111111111
                select_value_Y = random.choice(const_list)
                print("select_value_Y:{}".format(select_value_Y))
                print("value:{}".format(value))
                value_X = sympify(select_value_Y,evaluate = False) + sympify(value,evaluate = False)
                print("value_X:{}".format(value_X))
                substitution_expr = substitution_expr.replace("X", str(value_X))
                substitution_expr = substitution_expr.replace("Y", str(select_value_Y))

                substitution_dict[X]=value_X
                substitution_dict[Y]=select_value_Y
            elif key=="X + Y":
                select_value_Y = random.choice(const_list)
                value_X = sympify(value,evaluate = False) - sympify(select_value_Y,evaluate = False) 
                substitution_expr = substitution_expr.replace("X", str(value_X))
                substitution_expr = substitution_expr.replace("Y", str(select_value_Y))

                substitution_dict[X]=value_X
                substitution_dict[Y]=select_value_Y
            else:
                substitution_expr = substitution_expr.replace(key, value)
            expr = str(expr).replace(key, value)
 

        if "K" in substitution_expr:
            
            k =  random.randint(0,999)
            substitution_dict[K] = str(k)
            substitution_expr = substitution_expr.replace("K", str(k))
            print("substitution_expr2:{}".format(substitution_expr))
            print("type of substitution_expr2:{}".format(type(substitution_expr)))
            #substitution_expr = sympify(substitution_expr)
        
        #print("state:{}".format(state))
        new_state = state.replace(expr,substitution_expr)
        #print("new_state:{}".format(new_state))
    


    #print("==============================================end")
    return substitution_dict#new_state




import re
import random

def formula_parse(init_state):
    print("start===============================================================")
    print("init_state:{}".format(init_state))
    init_state_list = init_state.split("=")
    print("init_state_list:{}".format(init_state_list))
    print("end=================================================================")
    pattern = re.compile("\d*\(\d+/\d+\)\d*|\d+\.\d+%?|\d+%?|\d*\(\d+/\d+\)\d*|sin(.*)|cos(.*)")
    
    input_seq = []
    nums = []
    for s in init_state_list:
        print("state:{}".format(s))
        pos = re.search(pattern, s)
        if pos and pos.start() == 0:
            nums.append(s[pos.start(): pos.end()])
            input_seq.append("NUM")
            if pos.end() < len(s):
                input_seq.append(s[pos.end():])
        else:
            input_seq.append(s)
    print("input_seq:{}".format(input_seq))


const_list = [2*pi, pi, pi/2, pi/3, pi/6, -pi/6, -pi/3, -pi/2, -pi, -2*pi , pi/4, pi/5, pi/7, pi/8, pi/9, -pi/4, -pi/5, -pi/7, -pi/8, -pi/9]
X, Y, Z, K = symbols('X Y Z K')

def exchange_func(strs):
    
    Infix = strToInfix(strs)
    print("Infix:{}".format(Infix))
    postfix = infixToPostfix(Infix)
    #print("===================postfix:{}".format(postfix))
    stack = []
    priority = {'(': 0, ')': 0, 'sqrt(': 0,
                '+': 1, '-': 1,
                '*': 2, '/': 2, '^': 2}

    operators = priority.keys()
    denominators = []
    for token in postfix:
        if token in operators:
           if token not in ["(", ")", "+", 'sqrt(']:
              right = stack.pop()
              left = stack.pop()
              sub_formula = left + " " + token + " " + right
              stack.append(sub_formula)
           elif token == ")":
              sub_formula = stack.pop() + ")"
              stack.append(sub_formula)
           elif token == "(":
              sub_formula = "(" + stack.pop()
              stack.append(sub_formula)

           elif token == "sqrt(":
              sub_formula = "sqrt(" + stack.pop()
              stack.append(sub_formula)

           elif token == "+":
              right = stack.pop()
              left = stack.pop()
            #   print("right:{}".format(right))
            #   print("left:{}".format(left))
              if str(right) == "1": 
                 sub_formula = right + " " + token + " " + left
              else:
                 sub_formula = left + " " + token + " " + right
              #print("sub_formula:{}".format(sub_formula))
              stack.append(sub_formula)
              denominator = right.replace("^", "**").replace("0 -", "-")
              if not denominator.replace("**", "").replace("(", "").replace(")", "").replace("/", "").isdigit():
                 denominators.append(denominator)
              #denominators.append(right.replace(" ^ ", "**"))

        else:
           stack.append(token)

    print("stack[-1]: in exchange_func({}".format(stack[-1]))
    return stack[-1]#denominators




def adjust_formula(rule , substitution_expr):

    if rule == "tan(X/2)=sin(X)/(1+ cos(X))":
      Denominator =  Get_Denominators(substitution_expr)[0]
      print("Denominator:{}".format(Denominator))
      
      exchange_denominator=exchange_func(Denominator)
      print("exchange_denominator:{}".format(exchange_denominator))
      print("Denominator:{}".format(Denominator))
      print("substitution_expr:{}".format(substitution_expr))
      substitution_expr = substitution_expr.replace(" ", "")
      Denominator = Denominator.replace(" ", "")
      substitution_expr = substitution_expr.replace(Denominator, exchange_denominator)
      print("222substitution_expr:{}".format(substitution_expr))
      return substitution_expr

    return substitution_expr



import copy

def parse_and_replace(complete_expr, results):
    Infix = strToInfix(complete_expr)
    print("Infix:{}".format(Infix))
    Infix_new =  []
    for token in Infix:
        if token not in ['(', ')', 'sqrt(',
                         '+', '-',
                         '*', '/', '^', '**']:
            for key, value in zip(results.keys(), results.values()):
                token = token.replace(str(key),   "("+ str(sympify(value,evaluate = False)) +")")
            print("token:{}".format(token))

            if "K" in token:
                print("here======================3")
                print("sympify(value,evaluate = False):{}".format(sympify(value,evaluate = False)))
                select_value_K = sympify(random.randint(0,999),evaluate = False)#sympify("2")#sympify(random.randint(0,999))
                token = token.replace("K", str(select_value_K) )

                results[K] = select_value_K

            Infix_new.append(str(simplify_pi_parts_without_evaluating_trig(sympify(token,evaluate = False))))


        else:
            Infix_new.append(token)

    return Infix_new, results

    
def random_select_value(results):
    new_results = copy.deepcopy(results)
    print("here======================000")
    for key, value in zip(results.keys(), results.values()):
            print("key:{}".format(key))
            print("value:{}".format(value))
            print("type of value:{}".format(type(value)))
            if "Y" in str(value):
                print("here======================1")
                print("sympify(value,evaluate = False):{}".format(sympify(value,evaluate = False)))
                select_value_Y = sympify(random.choice(const_list),evaluate = False)#sympify(const_list[0]) #sympify(random.choice(const_list))
                new_value = sympify(str(value).replace("Y",  str(select_value_Y) ),evaluate = False) 
                value_X = new_value

                print("111111substitution_expr:{}".format(substitution_expr))
                new_results[X] = value_X
                new_results[Y] = select_value_Y

            elif "X" in str(value):
                print("here======================2")
                print("sympify(value,evaluate = False):{}".format(sympify(value,evaluate = False)))
                select_value_X = sympify(random.choice(const_list),evaluate = False)#sympify(const_list[1])#sympify(random.choice(const_list))
                new_value = sympify(str(value).replace("X", str(select_value_X)),evaluate = False)
                value_Y = new_value
                new_results[X] = select_value_X
                new_results[Y] = value_Y

            elif "K" in str(value):
                print("here======================3")
                print("sympify(value):{}".format(sympify(value)))
                select_value_K = sympify(random.randint(0,999),evaluate = False)#sympify("2")#sympify(random.randint(0,999))
                new_value = sympify(str(value).replace("K", str(select_value_K) ),evaluate = False)
                value_X = new_value
                new_results[X] = value_X
                new_results[K] = select_value_K
            else:
                new_results[key] = value
                
    return new_results
# expr = sin(X + Y)
# substitution_expr = sin(X)*cos(Y) + sin(Y)*cos(X)
# substitution = {X + Y: pi/2}
def replace_variables_by_parse(substitution, substitution_expr, expr):
    
    eq_list = []
    for key, value in zip(substitution.keys(), substitution.values()):
        print("key:{}".format(key))
        print("value:{}".format(value))
        if str(key)=="coef":
            continue

        eq = Eq(key, value)
        eq_list.append(eq)
        #print("eq:{}".format(eq))
    
    results = solve(eq_list, [X, Y])
    new_results = random_select_value(results)



    print("result in check_equations:{}".format(results))
    print("new_results in check_equations:{}".format(new_results))
    substitution_expr_new, new_results = parse_and_replace(substitution_expr, new_results)
    substitution_expr_new = (" ".join(substitution_expr_new)).replace("^", "**").replace("0 - ", "-")
    print("substitution_expr_new:{}".format(substitution_expr_new))
    expr_new, new_results  = parse_and_replace(expr, new_results)
    expr_new = (" ".join(expr_new)).replace("^", "**").replace("0 - ", "-")
    print("expr_new:{}".format(expr_new))




    print("=======================substitution_expr in check_equations:{}".format(substitution_expr_new))
    #print("=======================substitution_expr_adjust:{}".format(substitution_expr_adjust))
    print("=======================expr in check_equations:{}".format(expr_new))
    return new_results, substitution_expr_new, expr_new 





def replace_variables(substitution, substitution_expr, expr, state_side, axiom_rule):
    
    eq_list = []
    for key, value in zip(substitution.keys(), substitution.values()):
        print("key:{}".format(key))
        print("value:{}".format(value))
        if str(key)=="coef":
            continue

        eq = Eq(key, value)
        eq_list.append(eq)
        #print("eq:{}".format(eq))
    
    results = solve(eq_list, [X, Y])
    print("result in check_equations:{}".format(results))
    


    for key, value in zip(results.keys(), results.values()):
        print("key:{}".format(key))
        print("value:{}".format(value))
        print("type of value:{}".format(type(value)))
        if "Y" in str(value):
            print("here======================1")
            print("sympify(value,evaluate = False):{}".format(sympify(value,evaluate = False)))
            select_value_Y = sympify(random.choice(const_list),evaluate = False)#sympify(const_list[0]) #sympify(random.choice(const_list))
            new_value = sympify(str(value).replace("Y",  str(select_value_Y) ),evaluate = False) 
            value_X = new_value
            substitution_expr = substitution_expr.replace("X", "("+str(value_X)+")")
            substitution_expr = substitution_expr.replace("Y", "("+ str(select_value_Y)+")")

            print("111111substitution_expr:{}".format(substitution_expr))
            substitution[X] = value_X
            substitution[Y] = select_value_Y

        elif "X" in str(value):
            print("here======================2")
            print("sympify(value,evaluate = False):{}".format(sympify(value,evaluate = False)))
            select_value_X = sympify(random.choice(const_list),evaluate = False)#sympify(const_list[1])#sympify(random.choice(const_list))
            new_value = sympify(str(value).replace("X", str(select_value_X)),evaluate = False)
            value_Y = new_value
            substitution_expr = substitution_expr.replace("X",  "("+str(select_value_X)+")")
            substitution_expr = substitution_expr.replace("Y", "("+str(value_Y)+")")
            print("222222substitution_expr:{}".format(substitution_expr))
            substitution[X] = select_value_X
            substitution[Y] = value_Y

        elif "K" in str(value):
            print("here======================3")
            print("sympify(value):{}".format(sympify(value)))
            select_value_K = sympify(random.randint(0,999),evaluate = False)#sympify("2")#sympify(random.randint(0,999))
            new_value = sympify(str(value).replace("K", str(select_value_K) ),evaluate = False)
            value_X = new_value
            substitution_expr = substitution_expr.replace("X", "("+str(value_X)+")" )
            substitution_expr = substitution_expr.replace("K", str(select_value_K))
            print("333333substitution_expr:{}".format(substitution_expr))
            substitution[X] = value_X
            substitution[K] = select_value_K
        else:
            print("here======================4")
            print("sympify(value):{}".format(sympify(value,evaluate = False)))
            substitution_expr = str(sympify(substitution_expr.replace(str(key), "("+str(value)+")"),evaluate = False))
            print("444444substitution_expr:{}".format(substitution_expr))
            substitution[key] = value

        print("0=======================expr in check_equations for:{}".format(expr))
        expr = str(sympify(str(expr).replace(str(key),   "("+ str(sympify(value)) +")"),evaluate = False))   # sin(2 x) + sin(x)  = sympify(sin(2 pi2/5))   sin( 4pi/5)
        print("str(sympify(value)):{}".format(str(sympify(value),evaluate = False)))
        print("substitution_expr:{}".format(substitution_expr))
        print("1=======================expr in check_equations for:{}".format(expr))
    
    

    substitution_expr_adjust = adjust_formula(axiom_rule, substitution_expr)
    # placeholder = "PLACE_HOLDER"
        
    # result = str(perform(sympify(state_side), sympify(expr), sympify(placeholder)))
    # expr_test = state_side
    # result_else = result.split("PLACE_HOLDER")
    # print("result:{}".format(result))
    # print("result_else:{}".format(result_else))
    # for STR in result_else:
    #     if STR=="":
    #         continue
    #     else:
    #         expr_test = expr_test.replace(STR, "")
    # expr = expr_test.strip()
    # print("=======================expr_test:{}".format(expr_test))

    print("=======================substitution_expr in check_equations:{}".format(substitution_expr))
    print("=======================substitution_expr_adjust:{}".format(substitution_expr_adjust))
    print("=======================expr in check_equations:{}".format(expr))
    return substitution, substitution_expr_adjust, expr 






import re
def parse_coef_mul_bracket(complete_expr, expr):
    print("complete_expr:{}".format(complete_expr))
    print("expr:{}".format(expr))
    # print("complete_expr func:{}".format(complete_expr.func))
    # print("complete_expr args:{}".format(complete_expr.args))

    print("type complete_expr:{}".format(type(complete_expr)))
    print("type expr:{}".format(type(expr)))
    #complete_expr = str(complete_expr)
    #expr = str(expr)
    sub_expr_temp = None
    sub_expr_temp_old = None
    #a*k  + c + b*k
    #[a*(k) , b*(k)]
    # have a*k  #+ c + b*k: 
    for sub_expr in complete_expr.split(" "):
        #if expr in 
        # line="this hdr-biz 123 model server 456"
        # pattern=r"123"
        # matchObj = re.match(pattern, line)
        print("expr:{}".format(expr))
        print("sub_expr:{}".format(sub_expr))
        if sub_expr in ["+", "-", "*", "/"]:
           continue

        left_count = sub_expr.count("(")
        right_count = sub_expr.count(")")

        if left_count > right_count:
           sub_expr = sub_expr[1:]
        elif left_count< right_count:
           sub_expr = sub_expr[:-1]



        # matchObj = re.match("\w+" + expr, sub_expr)
        # print("matchObj:{}".format(matchObj))
        if expr in sub_expr:#matchObj!= None:
           #print("here=================================")
           sub_expr_temp = sub_expr
           break

    print("sub_expr_temp:{}".format(sub_expr_temp))
    print("expr:{}".format(expr))
    if sub_expr_temp != None and sub_expr_temp != expr:
       sub_expr_temp_old = sub_expr_temp
       sub_expr_temp = sub_expr_temp.replace(expr, "(" + expr + ")")
       print("after add bracket complete_expr:{}".format(sub_expr_temp))
       print("sub_expr_temp_old:{}".format(sub_expr_temp_old))

    return sub_expr_temp, sub_expr_temp_old

SPECIAL_TOKEN = "[REPLACE]"
def get_sub_match_str_mul_old(postfix, expr):
    print("===================postfix:{}".format(postfix))
    stack = []
    priority = {'(': 0, ')': 0,
                '+': 1, '-': 1,
                '*': 2, '/': 2, '^': 2}

    operators = priority.keys()
    sub_match_strs = []
    for token in postfix:
        if token in operators:
           if token not in ["(", ")", "+" , "-"]:
              right = stack.pop()
              left = stack.pop()
              sub_formula = left  + token  + right
              stack.append(sub_formula)
           elif token == ")":
              sub_formula = stack.pop() + ")"
              stack.append(sub_formula)
           elif token == "(":
              sub_formula = "(" + stack.pop()
              stack.append(sub_formula)
           elif token == "+" or token == "-" :
              right = stack.pop()
              left = stack.pop()
              
              right_temp = right.replace("^", "**").replace("0-", "-")
              left_temp = left.replace("^", "**").replace("0-", "-")
              print("right_temp:{}".format(right_temp))
              print("left_temp:{}".format(left_temp))
              print("expr:{}".format(expr))
              if (expr != right_temp) and (expr in right_temp): #and (not right_temp.replace("**", "").replace("(", "").replace(")", "").replace("/", "").isdigit()):
                 sub_match_strs.append(right_temp)
                #  print("expr:{}".format(expr))
                 
                #  print("expr in right:{}".format(expr in left))
                #  print("left111:{}".format(left))
                 right = right.replace(expr, SPECIAL_TOKEN)
                 #print("replace left:{}".format(left))

              if (expr != left_temp) and (expr in left_temp): #and (not left_temp.replace("**", "").replace("(", "").replace(")", "").replace("/", "").isdigit()):
                 sub_match_strs.append(left_temp)
                #  print("expr:{}".format(expr))
                 
                #  print("expr in right:{}".format(expr in right))
                #  print("right111:{}".format(right))
                 left = left.replace(expr, SPECIAL_TOKEN)
                # print("replace right:{}".format(right))

              sub_formula = left  + token  + right
              print("sub_formula:{}".format(sub_formula))
              stack.append(sub_formula)
        else:
           stack.append(token)
    
    last_temp = stack[-1].replace("^", "**").replace("0-", "-").replace("0 -", "-")
    if (expr != last_temp) and (expr.replace(" ","") in last_temp): #and (not right_temp.replace("**", "").replace("(", "").replace(")", "").replace("/", "").isdigit()):
        sub_match_strs.append(last_temp)

    print("stack[-1]: {}".format(stack[-1]))
    
    return sub_match_strs

def get_sub_match_str_mul(postfix, expr):
    print("===================postfix:{}".format(postfix))
    stack = []
    stack_without_placeholder =[]
    priority = {'(': 0, ')': 0, 'sqrt(': 0,
                '+': 1, '-': 1,
                '*': 2, '/': 2, '^': 2}

    operators = priority.keys()
    sub_match_strs = []
    sub_match_strs_old = []
    count = 1
    placeholder2term = dict()
    for token in postfix:
        if token in operators:
           if token not in ["(", ")", "+" , "-", 'sqrt(']:
              right = stack.pop()
              left = stack.pop()
              sub_formula = left  + token  + right
              stack.append(sub_formula)

              right = stack_without_placeholder.pop()
              left = stack_without_placeholder.pop()
              sub_formula = left  + token  + right
              stack_without_placeholder.append(sub_formula)
           elif token == ")":
              sub_formula = stack.pop() + ")"
              stack.append(sub_formula)

              sub_formula = stack_without_placeholder.pop() + ")"
              stack_without_placeholder.append(sub_formula)
           elif token == "(":
              sub_formula = "(" + stack.pop()
              stack.append(sub_formula)

              sub_formula = "(" + stack_without_placeholder.pop()
              stack_without_placeholder.append(sub_formula)

           elif token == "sqrt(":
              sub_formula = "sqrt(" + stack.pop()
              stack.append(sub_formula)

              sub_formula = "sqrt(" + stack_without_placeholder.pop()
              stack_without_placeholder.append(sub_formula)

           elif token == "+" or token == "-" :
              right = stack.pop()
              left = stack.pop()
              
              right_temp = right.replace("^", "**").replace("0-", "-")
              left_temp = left.replace("^", "**").replace("0-", "-")


              right_without_placeholder = stack_without_placeholder.pop()
              left_without_placeholder = stack_without_placeholder.pop()
              
              print("right_without_placeholder0:{}".format(right_without_placeholder))
              print("left_without_placeholder0:{}".format(left_without_placeholder))
            #   print("left_without_placeholder.replace(^, **):{}".format(left_without_placeholder.replace("^", "**")))
              #print("expr:{}".format(expr))
              right_temp_without_placeholder = (right_without_placeholder.replace("^", "**")).replace("0-", "-")
              left_temp_without_placeholder = (left_without_placeholder.replace("^", "**")).replace("0-", "-")

              print("right_without_placeholder1:{}".format(right_temp_without_placeholder))
              print("left_without_placeholder1:{}".format(left_temp_without_placeholder))
              
              print("right_temp:{}".format(right_temp))
              print("left_temp:{}".format(left_temp))
              print("expr:{}".format(expr))

             
 
              Flag, right_replace, count, placeholder2term = judge_existence(right_temp, expr, count, placeholder2term)
              if left_temp=="0" and token=="-":
                 Flag = False

              if (expr != right_temp) and (Flag==True): #and (left_temp!="0" and token!="-"): 
                 print("right_temp_without_placeholder:{}".format(right_temp_without_placeholder))
                 sub_match_strs_old.append(right_temp_without_placeholder)
                 sub_match_str = right_replace
                 for key in placeholder2term:
                 
                         sub_match_str = sub_match_str.replace(key, "("+str(placeholder2term[key])+")")
                 sub_match_strs.append(sub_match_str)
                 #sub_match_str = right_replace.

                 print("here================================1")
                 print("right_temp_without_placeholder:{}".format(right_temp_without_placeholder))
                 print("right_replace:{}".format(right_replace))
                 right = right_replace#right.replace(expr, SPECIAL_TOKEN)
                 #print("replace left:{}".format(left))

              Flag, left_replace, count, placeholder2term = judge_existence(left_temp, expr, count, placeholder2term)
              if (expr != left_temp) and (Flag==True): #and (not left_temp.replace("**", "").replace("(", "").replace(")", "").replace("/", "").isdigit()):
                 print("left_temp_without_placeholder:{}".format(left_temp_without_placeholder))
                 sub_match_strs_old.append(left_temp_without_placeholder.replace("^","**"))
                 print("here================================2")
                 
                 print("right_replace:{}".format(right_replace))
                 sub_match_str = left_replace
                 for key in placeholder2term:
                  
                         sub_match_str = sub_match_str.replace(key, "("+str(placeholder2term[key])+")")

                 sub_match_strs.append(sub_match_str)

                 left = left_replace#left.replace(expr, SPECIAL_TOKEN)
                # print("replace right:{}".format(right))

              sub_formula = left  + token  + right
              print("sub_formula:{}".format(sub_formula))
              stack.append(sub_formula)


              sub_formula = left_without_placeholder  + token  + right_without_placeholder
              stack_without_placeholder.append(sub_formula)
        else:
           stack.append(token)
           stack_without_placeholder.append(token)
    
    last_temp = stack[-1]
    last_temp_without_placeholder = stack_without_placeholder[-1]
    
    print("last_temp:{}".format(last_temp))
    print("expr:{}".format(expr))
    Flag, last_replace, count, placeholder2term = judge_existence(last_temp, expr, count, placeholder2term)
    
    print("expr:{}".format(expr))
    print("Flag:{}".format(Flag))
    if (expr != last_temp) and (Flag==True) : #and (not right_temp.replace("**", "").replace("(", "").replace(")", "").replace("/", "").isdigit()):
        sub_match_strs_old.append(last_temp_without_placeholder.replace("0-","-").replace("^","**").replace("0 -", "-"))
        sub_match_str = last_replace
        for key in placeholder2term:
          
                sub_match_str = sub_match_str.replace(key, "("+str(placeholder2term[key])+")")
        sub_match_strs.append(sub_match_str)

    print("stack[-1]:{}".format(stack[-1]))
    print("in mul sub_match_strs:{}".format(sub_match_strs))
    print("in mul sub_match_strs_old:{}".format(sub_match_strs_old))
    sub_match_strs_old.reverse()
    sub_match_strs.reverse()
    
    return sub_match_strs, sub_match_strs_old

base_str ='ABCDEFGHIGKLMNOPQRSTUVWXYZabcdefghigklmnopqrstuvwxyz'
length =len(base_str) -1
def judge_existence(sub_term, expr, count, placeholder2term, coef=None):
    placeholder = "a_placeholder" + "_" + base_str[random.randint(0, length)] +"_" + base_str[random.randint(0, length)]+"_" + base_str[random.randint(0, length)]
    placeholder_count = "a_placeholder"
    count_before = sub_term.count(placeholder_count)
    print("sub_term:{}".format(sub_term))
    if coef!=None:
        if ("sqrt(3)" in str(coef)) or  ("sqrt(2)" in str(coef)):
            coef_placeholder = sympify("99999999999999999",evaluate = False) 
            mul_expr = sympify(str(coef_placeholder*sympify(expr)).replace("99999999999999999", str(coef)),evaluate = False)
        else:
            mul_expr = coef*sympify(expr,evaluate = False)

        print("coef*sympify(expr):{}".format(coef*sympify(expr,evaluate = False)))
        result = str(perform(sympify(sub_term,evaluate = False), mul_expr, sympify(placeholder,evaluate = False)))
        print("result:{}".format(result))
    else:
       result = str(perform(sympify(sub_term,evaluate = False), sympify(expr,evaluate = False), sympify(placeholder,evaluate = False)))

    print("result:{}".format(sub_term))
    count_after = result.count(placeholder_count)

    if count_after > count_before:
        placeholder2term[placeholder] = expr
        return True, result, count+1, placeholder2term
    else:
        return False, None, count, placeholder2term


def get_sub_match_str_add(postfix, expr, coef=None):
    print("===================postfix:{}".format(postfix))
    stack = []
    stack_without_placeholder =[]
    priority = {'(': 0, ')': 0, "sqrt(":0,
                '+': 1, '-': 1,
                '*': 2, '/': 2, '^': 2}

    operators = priority.keys()
    sub_match_strs_old = []
    sub_match_strs = []
    count = 1
    placeholder2term = dict()
    for token in postfix:
        if token in operators:
           if token not in ["(", ")", "*" , "/", "sqrt("]:
              right = stack.pop()
              left = stack.pop()
              sub_formula = left  + token  + right
              stack.append(sub_formula.replace("0-", "-"))

              right = stack_without_placeholder.pop()
              left = stack_without_placeholder.pop()
              sub_formula = left  + token  + right
              stack_without_placeholder.append(sub_formula)
           elif token == ")":
              sub_formula = stack.pop() + ")"
              stack.append(sub_formula)

              sub_formula = stack_without_placeholder.pop() + ")"
              stack_without_placeholder.append(sub_formula)
           elif token == "(":
              sub_formula = "(" + stack.pop()
              stack.append(sub_formula)

              sub_formula = "(" + stack_without_placeholder.pop()
              stack_without_placeholder.append(sub_formula)
           elif token == "sqrt(":
              sub_formula = "sqrt(" + stack.pop()
              stack.append(sub_formula)

              sub_formula = "sqrt(" + stack_without_placeholder.pop()
              stack_without_placeholder.append(sub_formula)
           elif token == "*" or token == "/" :
              right = stack.pop()
              left = stack.pop()

              right_without_placeholder = stack_without_placeholder.pop()
              left_without_placeholder = stack_without_placeholder.pop()
 
              
              right_temp = right.replace("^", "**").replace("0-", "-")
              left_temp = left.replace("^", "**").replace("0-", "-")


              right_temp_without_placeholder = right_without_placeholder.replace("^", "**").replace("0-", "-")
              left_temp_without_placeholder = left_without_placeholder.replace("^", "**").replace("0-", "-")
              print("right_temp:{}".format(right_temp))
              print("left_temp:{}".format(left_temp))
              print("expr:{}".format(expr))

              Flag, right_replace, count, placeholder2term = judge_existence(right_temp, expr, count, placeholder2term, coef=coef)
              if left_temp=="0" and token=="-":
                 Flag = False

              if (expr != right_temp) and (Flag==True): #and (not right_temp.replace("**", "").replace("(", "").replace(")", "").replace("/", "").isdigit()):
                 sub_match_strs_old.append(right_temp_without_placeholder)
                 sub_match_str = right_replace
                 for key in placeholder2term:
                     if coef !=None:
                         sub_match_str = sub_match_str.replace(key, str(coef)+"*"+ "("+str(placeholder2term[key])+")")
                     else:
                         sub_match_str = sub_match_str.replace(key, "("+str(placeholder2term[key])+")")
                 sub_match_strs.append(sub_match_str)
                 #sub_match_str = right_replace.

                 print("here================================1")
                 print("right_temp_without_placeholder:{}".format(right_temp_without_placeholder))
                 print("right_replace:{}".format(right_replace))
                 right = right_replace#right.replace(expr, SPECIAL_TOKEN)
                 #print("replace left:{}".format(left))

              Flag, left_replace, count, placeholder2term = judge_existence(left_temp, expr, count, placeholder2term, coef=coef)
              if (expr != left_temp) and (Flag==True): #and (not left_temp.replace("**", "").replace("(", "").replace(")", "").replace("/", "").isdigit()):
                 sub_match_strs_old.append(left_temp_without_placeholder)
                 print("here================================2")

                 sub_match_str = left_replace#right_replace
                 for key in placeholder2term:
                     if coef !=None:
                         sub_match_str = sub_match_str.replace(key, str(coef)+"*"+ "("+str(placeholder2term[key])+")")
                     else:
                         sub_match_str = sub_match_str.replace(key, "("+str(placeholder2term[key])+")")

                 sub_match_strs.append(sub_match_str)

                 left = left_replace#left.replace(expr, SPECIAL_TOKEN)
                # print("replace right:{}".format(right))

              sub_formula = left  + token  + right
              print("sub_formula:{}".format(sub_formula))
              stack.append(sub_formula)


              sub_formula = left_without_placeholder  + token  + right_without_placeholder
              stack_without_placeholder.append(sub_formula)
        else:
           stack.append(token)
           stack_without_placeholder.append(token)
    

    last_temp = stack[-1]
    last_temp_without_placeholder = stack_without_placeholder[-1]
    Flag, last_replace, count, placeholder2term = judge_existence(last_temp, expr, count, placeholder2term, coef=coef)
    if (expr != last_temp) and (Flag==True): #and (not right_temp.replace("**", "").replace("(", "").replace(")", "").replace("/", "").isdigit()):
        sub_match_strs_old.append(last_temp_without_placeholder.replace("0-", "-").replace("^","**").replace("0 -", "-"))
        sub_match_str = last_replace
        for key in placeholder2term:
            if coef !=None:
                sub_match_str = sub_match_str.replace(key, str(coef)+"*"+ "("+str(placeholder2term[key])+")")
            else:
                sub_match_str = sub_match_str.replace(key, "("+str(placeholder2term[key])+")")
        sub_match_strs.append(sub_match_str)

    print("stack[-1]:{}".format(stack[-1]))
    print("sub_match_strs:{}".format(sub_match_strs_old))
    sub_match_strs_old.reverse()
    sub_match_strs.reverse()
    return sub_match_strs_old, sub_match_strs

def parse_coef_add_bracket_with_coef_by_postfix(complete_expr, expr, coef=None):

    complete_expr = str(complete_expr).strip()

    #Denominators = Get_Denominators(complete_expr)
    
    print("start==================================================")
    print("complete_expr:{}".format(complete_expr))
    print("expr:{}".format(expr))
    #print("Denominators:{}".format(Denominators))
    print("end====================================================")

    Infix = strToInfix(complete_expr)
    post_formula_str = infixToPostfix(Infix)
    #get_sub_match_str_add(complete_expr, expr)
    
    if coef == None:
        sub_expr_olds, sub_exprs  = get_sub_match_str_add(post_formula_str, expr)
        

    else:
        
        # 展开到原式子
        #expr_mul_coef = sympify(expr)*coef
        sub_expr_olds, sub_exprs = get_sub_match_str_add(post_formula_str, expr, coef=coef)

    sub_expr_temp = []
    sub_expr_temp_old = []
    sub_expr_set = set()
    for i, (sub_expr1, sub_expr_old) in  enumerate(zip(sub_exprs, sub_expr_olds)):
        flag = True
        for j, sub_expr2 in  enumerate(sub_exprs):
            if (sub_expr2 in sub_expr1) and (i!=j) and (sub_expr2 != sub_expr1):
                flag = False

        print("sub_expr1:{}".format(sub_expr1.replace(" ","")))
        print("sub_expr_old:{}".format(sub_expr_old.replace(" ","")))
        print("flag0:{}".format(flag))
        if (sub_expr1.replace(" ","") == sub_expr_old.replace(" ","")):
            print("Here====================================")
            flag = False
        print("flag1:{}".format(flag))
        if flag==True and (sub_expr1 not in sub_expr_set):
            sub_expr_set.add(sub_expr1)
            sub_expr_temp.append(sub_expr1)
            sub_expr_temp_old.append(sub_expr_old)



    print("sub_expr_temp:{}".format(sub_expr_temp))
    print("sub_expr_temp_old:{}".format(sub_expr_temp_old))
    if len(sub_expr_temp)!=0:
       return sub_expr_temp, sub_expr_temp_old#None
    else:
       return None, None


def parse_coef_mul_bracket_by_postfix_old(complete_expr, expr):
    complete_expr = str(complete_expr)
    Infix = strToInfix(complete_expr)
    post_formula_str = infixToPostfix(Infix)
    sub_match_strs = get_sub_match_str_mul(post_formula_str, expr)
    sub_match_strs_temp = []
    print("==============sub_match_strs0:{}".format(sub_match_strs))
    for i, str1 in enumerate(sub_match_strs):
        repeat_flag = False
        for j, str2 in enumerate(sub_match_strs):
            if str1 in str2 and i!=j:
               repeat_flag = True
               break
       
        if repeat_flag == False and str1!=post_formula_str:
           sub_match_strs_temp.append(str1)
    
    sub_match_strs = sub_match_strs_temp

    #complete_expr = str(complete_expr)
    #expr = str(expr)
    sub_expr_temp = []
    sub_expr_temp_old = []
    for sub_str_old in sub_match_strs:
        sub_expr_temp_old.append(sub_str_old)
        sub_str = sub_str_old.replace(expr.replace(" ",""), "(" + expr + ")")
        sub_expr_temp.append(sub_str)
        
    #a*k  + c + b*k
    #[a*(k) , b*(k)]
    # have a*k  #+ c + b*k: 
    print("sub_expr_temp:{}".format(sub_expr_temp))
    print("sub_expr_temp_old:{}".format(sub_expr_temp_old))
    
    if len(sub_expr_temp) == 0:
          return None, None
    else:
          return sub_expr_temp, sub_expr_temp_old

def parse_coef_mul_bracket_by_postfix(complete_expr, expr):
    Infix = strToInfix(str(complete_expr))
    print("Infix:{}".format(Infix))
    post_formula_str = infixToPostfix(Infix)
    print("post_formula_str:{}".format(post_formula_str))
    print("expr:{}".format(expr))
    sub_exprs, sub_expr_olds = get_sub_match_str_mul(post_formula_str, expr)
    
    sub_expr_temp = []
    sub_expr_temp_old = []
    print("sub_exprs:{}".format(sub_exprs))
    print("sub_expr_olds:{}".format(sub_expr_olds))
    sub_expr_set = set()
    for i, (sub_expr1, sub_expr_old) in  enumerate(zip(sub_exprs, sub_expr_olds)):
        flag = True
        for j, sub_expr2 in  enumerate(sub_exprs):
            if (sub_expr2 in sub_expr1) and (i!=j) and (sub_expr2 != sub_expr1):
                flag = False

        print("sub_expr1:{}".format(sub_expr1.replace(" ","")))
        print("sub_expr_old:{}".format(sub_expr_old.replace(" ","")))
        print("flag0:{}".format(flag))
        if (sub_expr1.replace(" ","") == sub_expr_old.replace(" ","")):
            print("Here====================================")
            flag = False
        print("flag1:{}".format(flag))
        if flag==True and (sub_expr1 not in sub_expr_set):
            sub_expr_set.add(sub_expr1)
            sub_expr_temp.append(sub_expr1)
            sub_expr_temp_old.append(sub_expr_old)

    print("sub_expr_temp in parse_coef_mul_bracket_by_postfix:{}".format(sub_expr_temp))
    print("sub_expr_temp_old in parse_coef_mul_bracket_by_postfix:{}".format(sub_expr_temp_old))
    return sub_expr_temp, sub_expr_temp_old

def parse_coef_add_bracket_with_coef(complete_expr, expr, coef):
    print("==========================================start in coef")
    print("complete_expr:{}".format(complete_expr))
    print("expr:{}".format(expr))
    print("coef:{}".format(coef))

    # print("expr:{}".format(expr))
    # print("coef:{}".format(coef))
    
    complete_expr = str(complete_expr)
    expr_mul_coef = str(sympify(expr)*coef,evaluate = False)
    expr = str(expr)
    coef = str(coef)

    expr_with_coef = coef + "*" +"(" + expr + ")"
    print("expr_with_coef:{}".format(expr_with_coef))
    print("expr_mul_coef:{}".format(expr_mul_coef))

    complete_expr_add_bracket_with_coef = complete_expr.replace(expr_mul_coef.strip(), expr_with_coef)
    print("complete_expr_add_bracket_with_coef:{}".format(complete_expr_add_bracket_with_coef))
    print("==========================================end in coef")
    
    if complete_expr_add_bracket_with_coef!= complete_expr:
       return complete_expr_add_bracket_with_coef, complete_expr#sub_expr_temp, sub_expr_temp_old
    else:
       return None, None


def parse_coef_add_bracket_with_coef_by_postfix_old(complete_expr, expr, coef=None):
    
    complete_expr = complete_expr.strip()
    if coef == None:
        sub_formula = perform(sympify(complete_expr,evaluate = False), sympify(expr,evaluate = False), sympify("a_placeholder",evaluate = False))
        sub_formula = str(sub_formula).replace("a_placeholder", expr)
        print("sub_formula:{}".format(sub_formula))
    else:
        # 展开到原式子
        expr_mul_coef = sympify(expr,evaluate = False)*coef

        sub_formula = perform(sympify(complete_expr,evaluate = False), expr_mul_coef, sympify("a_placeholder",evaluate = False))
        expr_with_coef = str(coef) + "*" +"(" + expr + ")"
        sub_formula = str(sub_formula).replace("a_placeholder", expr_with_coef)
        print("sub_formula:{}".format(sub_formula))

    if sub_formula!= complete_expr:
       return [sub_formula], [complete_expr]#None
    else:
       return None, None


add_sub_bracket_list=["sin(X) + sin(Y)=2*sin(X/2 + Y/2)*cos(X/2 - Y/2)", "sin(X) - sin(Y)=2*sin(X/2 - Y/2)*cos(X/2 + Y/2)", "cos(X) + cos(Y)=2*cos(X/2 - Y/2)*cos(X/2 + Y/2)", "cos(X) - cos(Y)=-2*sin(X/2 - Y/2)*sin(X/2 + Y/2)", "tan(X) + tan(Y)=(-tan(X)*tan(Y) + 1)*tan(X + Y)", "tan(X) - tan(Y)=(tan(X)*tan(Y) + 1)*tan(X - Y)", "tan(X) - tan(Y)=sin(X - Y)/(cos(X)*cos(Y))"]
def formula_substitution(state_list, result, substitution_expr, expr, i, axiom_rule):
    new_state = None
    new_results = []
    for substitution in result:
       #print("=============================================substitution key:{}".format(substitution.keys()[0]))
       if (not substitution) or (str(list(substitution.values())[0])=="0"):
          continue
       new_results.append(substitution)
    
    substitution_dict = dict()
    expr_with_bracket=None
    expr_with_bracket_old=None
    if len(new_results)>0:
        #print("here===========================1")
        substitution = random.choice(new_results)#new_results[0]#random.choice(new_results)
        print("select substitution:{}".format(substitution))
        print("before expr:{}".format(expr))
        print("before substitution_expr:{}".format(substitution_expr))
        substitution_dict, substitution_expr, expr  = replace_variables_by_parse(substitution, substitution_expr, expr) #replace_variables(substitution, substitution_expr, expr, state_list[i], axiom_rule)
        print("after expr:{}".format(expr))
        print("after substitution_expr:{}".format(substitution_expr))
        if "K" in substitution_expr:
            k =  random.randint(0,999)
            substitution_dict[K] = sympify(k,evaluate = False)
            substitution_expr = substitution_expr.replace("K", str(k))
            # print("substitution_expr2:{}".format(substitution_expr))
            # print("type of substitution_expr2:{}".format(type(substitution_expr)))
        
        #substitution_expr = sympify(substitution_expr)
        #expr = sympify(expr)
        print("state in replace:{}".format(state_list))
        print("expr in replace:{}".format(expr))
        print("substitution_expr in replace:{}".format(substitution_expr))
        # 进行公示替换
        #state_Eq = Eq(sympify(state.split("=")[0]), sympify(state.split("=")[1]))
        #print("substitution.keys():{}".format(substitution.keys()))
        if axiom_rule in add_sub_bracket_list:
           print("=============================================================coef")
           print("=======================================start")
           print("state_list:{}".format(state_list))
           print("expr:{}".format(expr))
           print("substitution_expr:{}".format(substitution_expr))
           print("=========================================end")

           if "coef" in substitution.keys() :
                replace_result = perform(sympify(state_list[i],evaluate = False), substitution["coef"]*sympify(expr,evaluate = False), substitution["coef"]*sympify(substitution_expr,evaluate = False))
                print("==================================================================start")
                print("state_list[i]:{}".format(state_list[i]))
                print("expr:{}".format(expr))
                print("substitution_expr:{}".format(substitution_expr))
                print("coef:{}".format(substitution["coef"]))
                print("replace_result:{}".format(replace_result))
                expr_with_bracket, expr_with_bracket_old = parse_coef_add_bracket_with_coef_by_postfix(state_list[i], expr, coef=substitution["coef"])#parse_coef_add_bracket(sympify(state_list[i]), substitution["coef"]*expr)
           else:
                print("==================================================================start")
                print("state_list[i]:{}".format(state_list[i]))
                print("expr:{}".format(expr))
                replace_result = perform(sympify(state_list[i],evaluate = False), sympify(expr,evaluate = False), sympify(substitution_expr,evaluate = False))
                expr_with_bracket, expr_with_bracket_old = parse_coef_add_bracket_with_coef_by_postfix(state_list[i], expr)
        #    expr = substitution["coef"]*expr
        #    substitution = substitution["coef"]*substitution_expr
           print("expr1:{}".format(expr))
           print("substitution_expr1:{}".format(substitution_expr))
           print("===================================================================end")
        else:
           replace_result = perform(sympify(state_list[i],evaluate = False), sympify(expr,evaluate = False), sympify(substitution_expr,evaluate = False))
           print("=======================================start")
           print("state_list:{}".format(state_list))
           print("expr:{}".format(expr))
           print("substitution_expr:{}".format(substitution_expr))
           print("=========================================end")
           expr_with_bracket, expr_with_bracket_old = parse_coef_mul_bracket_by_postfix(state_list[i], expr)
           print("expr_with_bracket:{}".format(expr_with_bracket))
           print("expr_with_bracket_old:{}".format(expr_with_bracket_old))
        
        
        print("replace_result:{}".format(replace_result))
        state_list[i] = replace_result
        new_state = str(state_list[0]) + "=" + str(state_list[1])
        #new_state = state.replace(expr,substitution_expr)
        print("new_state:{}".format(new_state))




    substitution_dict["new_state"] = new_state
    substitution_dict["left"] = expr
    substitution_dict["right"] = substitution_expr
    substitution_dict["i"] = i 

    print("substitution_dict:{}".format(substitution_dict))
    #print("==============================================end")
    return substitution_dict, expr_with_bracket, expr_with_bracket_old#new_state


def formula_substitution_by_sympy(state_list, result, substitution_expr, expr, i):
    new_state = None
    new_results = []
    for substitution in result:
       if not substitution:
          continue
       new_results.append(substitution)
    
    substitution_dict = dict()
    #print("here===========================0")
    if len(new_results)>0:
        #print("here===========================1")
        substitution = random.choice(new_results)
        print("select substitution:{}".format(substitution))
        
        substitution_dict, substitution_expr, expr  = replace_variables(substitution, substitution_expr, expr)
        if "K" in substitution_expr:
            k =  random.randint(0,999)
            substitution_dict[K] = sympify(k,evaluate = False)
            substitution_expr = substitution_expr.replace("K", str(k))
            # print("substitution_expr2:{}".format(substitution_expr))
            # print("type of substitution_expr2:{}".format(type(substitution_expr)))
        
        substitution_expr = sympify(substitution_expr,evaluate = False)
        expr = sympify(expr,evaluate = False)
        print("state in replace:{}".format(state_list))
        print("expr in replace:{}".format(expr))
        print("substitution_expr in replace:{}".format(substitution_expr))
        # 进行公示替换
        #state_Eq = Eq(sympify(state.split("=")[0]), sympify(state.split("=")[1]))
        #print("substitution.keys():{}".format(substitution.keys()))
        if "coef" in substitution.keys():
           #print("here================================coef")
           replace_result = perform(sympify(state_list[i],evaluate = False), substitution["coef"]*expr, substitution["coef"]*substitution_expr)
           expr = substitution["coef"]*expr
           substitution = substitution["coef"]*substitution_expr
        else:
           replace_result = perform(sympify(state_list[i],evaluate = False), expr, substitution_expr)

        print("replace_result:{}".format(replace_result))
        state_list[i] = replace_result
        new_state = str(state_list[0]) + "=" + str(state_list[1])
        #new_state = state.replace(expr,substitution_expr)
        print("new_state:{}".format(new_state))

    #print("here===========================2")
    substitution_dict["new_state"] = new_state
    substitution_dict["left"] = expr
    substitution_dict["right"] = substitution_expr
    substitution_dict["i"] = i 
    #print("==============================================end")
    return substitution_dict#new_state



def Get_num_goals(tactic_state):
    return tactic_state.count("⊢")

def get_goals(tactic_state):
    #print("tactic_state.split(⊢):{}".format(tactic_state.split("⊢")))
    return tactic_state.split("⊢")[1:]

def count_inequality(tactic_state):
    #print("tactic_state:{}".format(tactic_state))
    goals = get_goals(tactic_state)
    goals_temp = []

    #print("goals:{}".format(goals))
    count = 0
    for goal in goals:
        goal = goal.split("\n\n")[0]
        if "≠" in goal:
           count +=1
        #print("goal:{}".format(goal))

    return count


# 执行lean_gym
def excute_lean_gym(leanserver, tactics, output_state, last_state=None, tactics_with_bracket_prove_len=0):#search_id, tactic_state_id):
    print("excute here====================================")
    search_id = output_state["search_id"]
    tactic_state_id = output_state["tactic_state_id"]
    print("tactics:{}".format(tactics))
    lean_output = None

    subgoal_proofed = False
    excute_tactics = []
    excute_tactics_record =[]
    #jump_rw_flag = False
    subgoal_proofed_stack = [False]
    for  i, tactic in enumerate(tactics):
        tactic = tactic.replace("π", "pi")
        
        if tactic == "tidy":
           tactic = "focus{tidy}"

        if tactic == "repeat {apply congr_arg _}":
           tactic = "focus{repeat {apply congr_arg _}}"

        if tactic=="{" :#or tactic=="},":
            excute_tactics.append("{")
            if subgoal_proofed_stack[-1] == True:
               subgoal_proofed_stack.append(True)
            else:
               subgoal_proofed_stack.append(False)
            continue

        if tactic == "},":
            # subgoal_proofed == False表示括号里的没有证完
            if subgoal_proofed_stack[-1]==False:#subgoal_proofed == False:
               #assert 1==0
               # 表示这里错误, 返回None
               return None, None, None
            subgoal_proofed_stack.pop()
            

        if subgoal_proofed_stack[-1] and (tactic!="repeat {assumption}") :#subgoal_proofed and (tactic!="repeat {assumption}") :
            continue

        if tactic == "repeat {assumption}" and (count_inequality(output_state["tactic_state"])==0):
            continue

        if "suffices:" not in tactic:
           print("tactic:{}===========================================append here".format(tactic))
           excute_tactics.append(tactic)
        
        excute_tactics_record.append(tactic)
        if tactic=="repeat {apply congr_arg _}":
           goals  = get_goals(output_state["tactic_state"])
           print("===========after get goals:{}".format(goals))
           flag = False
           for goal in goals:
               if "≠" not in goal:
                    expressions = goal.split("=") 
                    print("goal:{}".format(expressions))
                    new_expressions = [expressions[0].strip(), expressions[1].strip()]

                    if new_expressions[0][0] == "-" and new_expressions[1][0] == "-":
                        tactic="apply congr_arg _"#flag = True

        #print("output_state in excute_lean_gym:{}".format(output_state))
        n_inequality_goals_before_tactic = count_inequality(output_state["tactic_state"])
        n_goals_before_tactic = Get_num_goals(output_state["tactic_state"])
        lean_output  = leanserver.run_tac(search_id, tactic_state_id, tactic)
        error_message = lean_output["error"]
       
        if error_message is not None:
           print("tactic:{}".format(tactic))
           break
           #assert 1==0

        n_goals_after_tactic = Get_num_goals(lean_output["tactic_state"])
        n_inequality_goals_after_tactic = count_inequality(lean_output["tactic_state"])
        print("tactic:{}".format(tactic))
        print("n_goals_before_tactic:{}".format(n_goals_before_tactic))
        print("n_inequality_goals_before_tactic:{}".format(n_inequality_goals_before_tactic))
        print("n_goals_after_tactic:{}".format(n_goals_after_tactic))
        print("n_inequality_goals_after_tactic:{}".format(n_inequality_goals_after_tactic))
        
        print("last_state:{}".format(last_state))
        tactic_state_id = lean_output["tactic_state_id"]
        
        print("(n_goals_before_tactic - n_inequality_goals_before_tactic):{}".format((n_goals_before_tactic - n_inequality_goals_before_tactic)))
        print("(n_goals_after_tactic - n_inequality_goals_after_tactic):{}".format((n_goals_after_tactic - n_inequality_goals_after_tactic)))

        print("========lean_output:{}".format(lean_output))

        if ((n_goals_after_tactic- n_inequality_goals_after_tactic) < (n_goals_before_tactic-n_inequality_goals_before_tactic)):# and  (tactic!="repeat {assumption}"):
           subgoal_proofed_stack[-1] = True
       
        output_state = lean_output
    
    print("in lean_gym excute_tactics:{}".format(excute_tactics))
    # 在这里跳过了一些东西 
    return (lean_output, excute_tactics[tactics_with_bracket_prove_len+2:-2], excute_tactics_record)

def process_all_tactics(all_tactics):
    all_new_tactics = []
    for tactic in all_tactics:
        if tactic == "{" :
           all_new_tactics.append(tactic)
           continue
           
        if tactic[-1]!=",":
              tactic = tactic + ","

        all_new_tactics.append(tactic)

    return all_new_tactics
    
# axiom.rule:sin(X)*cos(Y)=sin(X - Y)/2 + sin(X + Y)/2
# {X + Y: 0, X - Y: pi/2}

# axiom.rule:sin(X) + sin(Y)=2*sin(X/2 + Y/2)*cos(X/2 - Y/2)
# state:sin(pi/4 - pi/4)/2 + sin(pi/4 + pi/4)/2=1/2
import os
def read_data(file_path):
    dir_list = os.listdir(file_path)
    print("dir_list:{}".format(dir_list))
    prove_tactic_temp = []
    decl2data = dict()
    init_state2decl = dict()
    init_states = []
    decl_name = None
    for file_name in dir_list:
        #print("file_name:{}".format(file_name[-5:]))
        if file_name[-5:] == ".lean" and file_name != "all_trigo.lean" and file_name != "trigo_import.lean" and file_name != "unlabel_test.lean":
           final_file_name = file_path + "/" + file_name
           with open (file = final_file_name, mode = "r", encoding = "utf-8") as file:
               data = file.read()
               for line in data.split("\n"):
                    if line == "import trigo_import" or line == "open real" or line == "open_locale real" or line == "variables (x y : ℝ)":
                       continue
                    
                    if "lemma" in line:
                        #print("line:{}".format(line))
                        init_prove_state = line.split("lemma ")[1]
                        init_prove_states = init_prove_state.split(": ")
                        if "(" in init_prove_states[0]:
                             decl_name = init_prove_states[0].split(" (")[0]
                             #print("decl_name:{}".format(decl_name))
                        else:
                             decl_name = init_prove_states[0]
                        
                        init_state = init_prove_states[-1].split(":=")[0]
                        init_state2decl[init_state] = decl_name 
                        #print("init_state:{}".format(init_state))
                        init_states.append(init_state)
                        prove_tactic_temp = []

                    elif "begin" in line or line == "":
                        continue 
                    elif "end" in line:
                        decl2data[decl_name] = prove_tactic_temp
                    else:
                        prove_tactic_temp.append(line.strip())
    print("len of init_states:{}".format(len(init_states)))
    return decl2data, init_states, init_state2decl


def parse_denominator(formula_list, denominators_parsed):
    pattern = "\)/\(.*\)"
    pattern_bucket = '([()])∗'

    for formula in formula_list:
        formula = formula.replace(" ","")
        #print("formula:{}".format(formula))
        denominators = re.findall(pattern, formula)#tokens(formula)#re.findall(pattern, formula)
        new_denominators = []
        #print("denominators:{}".format(denominators))
        for denominator in denominators:
            sub_formula = ")/".join(denominator.split(")/")[1:])
            #print("sub_formula:{}".format(sub_formula))
            

            new_denominators.append(sub_formula[1:-1])

        denominators_parsed.extend(new_denominators)
        #print("new_denominators:{}".format(new_denominators))
        parse_denominator(new_denominators, denominators_parsed)
    
    #print("denominators_parsed:{}".format(denominators_parsed))
    #return denominators_parsed

from utils_trigo import get_denominators

def get_denominator(formula_list, denominators_parsed):
    for formula in formula_list:
        #print("formula:{}".format(formula))
        formula_new = get_denominators(formula)
        denominators_parsed.extend(formula_new)
        get_denominator(formula_new, denominators_parsed)

positive_prove_list = ["cos(X - Y)=sin(X)*sin(Y) + cos(X)*cos(Y)", "cos(X + Y)=-sin(X)*sin(Y) + cos(X)*cos(Y)", "sin(X - Y)=sin(X)*cos(Y) - sin(Y)*cos(X)", "sin(X + Y)=sin(X)*cos(Y) + sin(Y)*cos(X)"]
def get_prove_tactic_old(rule_name, tactics, i):
    #["have : "+ str(substitution_dict["right"]) + "  =  " + str(substitution_dict["left"])+","] + ["{"] + tactics + ["},"] + ["rw this,"]
    print("===rule_name:{}".format(rule_name))
    print("===tactics:{}".format(tactics))
    if rule_name not in positive_prove_list:
         if i==0: 
            tactics = ["have : "+ str(substitution_dict["right"]) + "  =  " + str(substitution_dict["left"])+","] + ["{"] + tactics + ["},"] + ["conv {to_lhs, rw this,}"]#["rw this,"]
         else:
            tactics = ["have : "+ str(substitution_dict["right"]) + "  =  " + str(substitution_dict["left"])+","] + ["{"] + tactics + ["},"] + ["conv {to_rhs, rw this,}"]#["rw this,"]
    else:
         if i==0:
            tactics = ["have : "+ str(substitution_dict["left"]) + "  =  " + str(substitution_dict["right"])+","] + ["{"] + tactics + ["},"] + ["conv {to_lhs, rw ← this,}"]#["rw ← this,"]
         else:
            tactics = ["have : "+ str(substitution_dict["left"]) + "  =  " + str(substitution_dict["right"])+","] + ["{"] + tactics + ["},"] + ["conv {to_rhs, rw ← this,}"]#["rw ← this,"]

    return tactics

def get_prove_tactic(rule_name, tactics, i):
    #["have : "+ str(substitution_dict["right"]) + "  =  " + str(substitution_dict["left"])+","] + ["{"] + tactics + ["},"] + ["rw this,"]
    print("===rule_name:{}".format(rule_name))
    print("===tactics:{}".format(tactics))
    if rule_name not in positive_prove_list:
         if i==0: 
            tactics = ["have : "+ str(substitution_dict["left"]) + "  =  " + str(substitution_dict["right"])+","] + ["{"] + tactics + ["},"] + ["conv {to_lhs, rw ← this,}"]#["rw this,"]
         else:
            tactics = ["have : "+ str(substitution_dict["left"]) + "  =  " + str(substitution_dict["right"])+","] + ["{"] + tactics + ["},"] + ["conv {to_rhs, rw ← this,}"]#["rw this,"]
    else:
         if i==0:
            tactics = ["have : "+ str(substitution_dict["left"]) + "  =  " + str(substitution_dict["right"])+","] + ["{"] + tactics + ["},"] + ["conv {to_lhs, rw ← this,}"]#["rw ← this,"]
         else:
            tactics = ["have : "+ str(substitution_dict["left"]) + "  =  " + str(substitution_dict["right"])+","] + ["{"] + tactics + ["},"] + ["conv {to_rhs, rw ← this,}"]#["rw ← this,"]

    return tactics

def get_prove_tactic_init(rule_name, tactics, substitution_left_expr, substitution_right_expr):
    
    print("===rule_name:{}".format(rule_name))
    print("In init ===tactics:{}".format(tactics))


    if rule_name not in positive_prove_list:
            tactics = ["have : "+ substitution_left_expr + "  =  " + substitution_right_expr +","] + ["{"] + tactics + ["},"] + ["rw this,"]
    else:
            tactics = ["have : "+ substitution_left_expr + "  =  " + substitution_right_expr +","] + ["{"] + tactics + ["},"] + ["rw ← this,"]

    return tactics

def Judge_equivalent(leanserver, left, right, lean_output):
    
    search_id = lean_output["search_id"]
    tactic_state_id = lean_output["tactic_state_id"]

    judge_tactics =  ["have : "+ left + "  =  " + right +","]  + ["refl,"]  
    flag = True

    n_goals_before_tactic = Get_num_goals(lean_output["tactic_state"])

    for i, tactic in enumerate(judge_tactics):
        
        lean_output  = leanserver.run_tac(search_id, tactic_state_id, tactic)
        error_message = lean_output["error"]
        if error_message != None:
            flag = False
            print("lean_output:{}".format(lean_output))
            print("tactic:{}".format(tactic))
            assert i == 1
        
        tactic_state_id = lean_output["tactic_state_id"]
    return flag   


    if flag == True:
       
       n_goals_after_tactic = Get_num_goals(lean_output["tactic_state"])
       if (n_goals_after_tactic < n_goals_before_tactic) :
           return True
       else:
           return False
    else:
       return False

 



def get_denominator_from_lean_gym(formula_list):

    denominators_set = []
    for formula in formula_list:
        formula = formula.replace("cos ","cos")
        formula = formula.replace("sin ","sin")
        
        search_results = re.finditer(r' \(.*?\)⁻¹', formula) 
        for item in search_results: 
            item = item.group(0)
            if item.count("(")>item.count(")"):
               item = item.strip()[1:] 
            denominators_set.append(item.strip())
    denominators_set = list(set(denominators_set))
    #print("denominators_set:{}".format(denominators_set))
    return denominators_set

def ParseNestedParen(string, level):
    """
    Generate strings contained in nested (), indexing i = level
    """
    if len(re.findall("\(", string)) == len(re.findall("\)", string)):
        LeftRightIndex = [x for x in zip(
        [Left.start()+1 for Left in re.finditer('\(', string)], 
        reversed([Right.start() for Right in re.finditer('\)', string)]))]

    elif len(re.findall("\(", string)) > len(re.findall("\)", string)):
        return ParseNestedParen(string + ')', level)

    elif len(re.findall("\(", string)) < len(re.findall("\)", string)):
        return ParseNestedParen('(' + string, level)

    else:
        return 'fail'

    return [string[LeftRightIndex[level][0]:LeftRightIndex[level][1]]]



def ParsePairBrackets(s1):
    if s1.count("(") != s1.count(")"):
         s2 = ParseNestedParen(s1, 0)
         s3 = ParsePairBrackets(s2)
    else:
         return s1

# import sympy as sp
# s = sp.Symbol('s', rational=True)
# eq=1/(2*s**2 + 3*s + 4)
# top, bot = [[float(i) for i in sp.Poly(i, s).all_coeffs()] for i in eq.as_numer_denom()]
# import control as co
# co.TransferFunction(top, bot) 


def init_state_function(axiom):
    name_space = "real"
    lean_output = leanserver.init_search("original_data", name_space)
    lean_output  = leanserver.run_tac(lean_output["search_id"], lean_output["tactic_state_id"], "intros")
    
    rule = axiom.rule
    has_nonzero = axiom.has_nonzero


    #print("rule:{}".format(rule))
    substitution = dict()
    left_expr, right_expr = rule.split("=")
    print("left_expr:{}".format(left_expr))
    print("right_expr:{}".format(right_expr))
    if "X" in rule:
       value_X = random.choice(const_list) 
       substitution[sympify("X",evaluate = False)] = sympify(str(value_X),evaluate = False)

    if "Y" in rule:
       value_Y = None
       for i in  range(1000):
           value_Y = random.choice(const_list)
           if str(value_Y) != str(value_X):
              break 
       substitution[sympify("Y",evaluate = False)] = sympify(str(value_Y),evaluate = False)


    if "K" in rule:
       value_K = str(random.randint(0,1000))
       substitution[sympify("K",evaluate = False)] = sympify(str(value_K),evaluate = False)

    substitution_left_expr, substitution = parse_and_replace(left_expr, substitution)
    substitution_right_expr, substitution = parse_and_replace(right_expr, substitution)

    substitution_left_expr = (" ".join(substitution_left_expr)).replace("0 -","-")
    substitution_right_expr = (" ".join(substitution_right_expr)).replace("0 -","-")
    print("substitution_left_expr:{}".format(substitution_left_expr))
    print("substitution_right_expr:{}".format(substitution_right_expr))


    new_state = substitution_left_expr + "=" + substitution_right_expr
    problem_conditions_all = []
    if has_nonzero:
        non_zeros = axiom.get_nonzero(substitution, None, None) 
        for non_zero in non_zeros:
            problem_conditions_all.append(non_zero)

    init_axiom_tactics = axiom.get_tactics(substitution, substitution_left_expr, substitution_right_expr)
    init_axiom_tactics =  ["have : "+ substitution_left_expr + "  =  " + substitution_right_expr +","] + ["{"] + init_axiom_tactics + ["},"] + ["rw this,"]
    tactics_forward = ["have : "+ substitution_left_expr + "  =  " + substitution_right_expr +","]  
    
    print("============================================================init_axiom_tactics:{}".format(init_axiom_tactics))
    _, excute_tactics, lean_output_ = excute_lean_gym(leanserver, init_axiom_tactics, lean_output)
    lean_output, _, _ = excute_lean_gym(leanserver, tactics_forward, lean_output)  #excute_lean_gym(tactics)
    
    
    print("============================================================init excute_tactics:{}".format(excute_tactics))
    print("============================================================init lean_output_:{}".format(lean_output_))
    # 在这里传入i
    tactics_prove = get_prove_tactic_init(axiom.rule, excute_tactics, substitution_left_expr, substitution_right_expr)

    print("init lean_output:{}".format(lean_output))
    print("new_state:{}".format(new_state))
    print("substitution:{}".format(substitution))
    return  lean_output,  tactics_prove, new_state, problem_conditions_all#lean_output,  init_axiom_tactics, new_state, problem_conditions_all

import json 
from lean_server import *
import copy
import random
import argparse


if __name__ == "__main__":
    bracket_list=["sin(X)*sin(Y)=cos(X - Y)/2 - cos(X + Y)/2", "sin(X)*cos(Y)=sin(X - Y)/2 + sin(X + Y)/2", "cos(X)*cos(Y)=cos(X - Y)/2 + cos(X + Y)/2", "sin(Y)*cos(X)=-sin(X - Y)/2 + sin(X + Y)/2", "tan(X)*tan(Y)=(tan(X) - tan(Y))/tan(X - Y) - 1", "tan(X)*tan(Y)=-(tan(X) + tan(Y))/tan(X + Y) + 1",
                  "sin(X) + sin(Y)=2*sin(X/2 + Y/2)*cos(X/2 - Y/2)", "sin(X) - sin(Y)=2*sin(X/2 - Y/2)*cos(X/2 + Y/2)", "cos(X) + cos(Y)=2*cos(X/2 - Y/2)*cos(X/2 + Y/2)", "cos(X) - cos(Y)=-2*sin(X/2 - Y/2)*sin(X/2 + Y/2)", "tan(X) + tan(Y)=(-tan(X)*tan(Y) + 1)*tan(X + Y)", "tan(X) - tan(Y)=(tan(X)*tan(Y) + 1)*tan(X - Y)", "tan(X) - tan(Y)=sin(X - Y)/(cos(X)*cos(Y))"   ,  
                  "sin(X)/cos(X)=tan(X)", 'sin(X)**2 + cos(X)**2=1']
    
    bad_init_axiom = ['tan(2*X)=2*tan(X)/(1 - tan(X)**2)', 'tan(X/2)=(1 - cos(X))/sin(X)', 'tan(X/2)=sin(X)/(1+ cos(X))', 'tan(X - Y)=(tan(X) - tan(Y))/(1 + tan(X)*tan(Y))', 'Abs(X)=X', 'tan(X) + tan(Y)=(-tan(X)*tan(Y) + 1)*tan(X + Y)', 'tan(X) - tan(Y)=(tan(X)*tan(Y) + 1)*tan(X - Y)', 'tan(X) - tan(Y)=sin(X - Y)/(cos(X)*cos(Y))', 'tan(X)*tan(Y)=(tan(X) - tan(Y))/tan(X - Y) - 1', 'tan(X)*tan(Y)=-(tan(X) + tan(Y))/tan(X + Y) + 1']
    decl2generated_tactics = dict()
    decl2generated_states = dict()
    decl2generated_all_tactics = dict()
    leanserver = LeanServer()
    all_data_list = []
    all_bad_data = []
    
    
    parser = argparse.ArgumentParser()
    parser.add_argument('--try_times', type=int, default=2)
    parser.add_argument('--prove_count', type=int, default=1)
    parser.add_argument('--file_name', type=str, default="")
    
    args = parser.parse_args()
    
    try_times = args.try_times     #1000
    prove_count = args.prove_count
    
    for count in range(try_times):#i in range(0, 20):
        all_tactics = []
        rule_list = [rule_name.rule for rule_name in tactic_converter_list]
        rule2name = dict(zip(rule_list,tactic_converter_list))
        init_axiom = None
        while True:
              init_axiom = random.choice(tactic_converter_list) #rule2name["tan(2*pi/3)=-sqrt(3)"]#random.choice(tactic_converter_list)#rule2name["sin(X)=sin(2*X)/(2*cos(X))"] #random.choice(tactic_converter_list) #rule2name["tan(X)*tan(Y)=-(tan(X) + tan(Y))/tan(X + Y) + 1"]#random.choice(tactic_converter_list)
             
              if init_axiom.rule=="A=X" or init_axiom.rule=="Abs(X)=-X" or init_axiom.rule=="ABC" :
                  continue

              try:
                  lean_output,  init_axiom_tactics, state, problem_conditions_all = init_state_function(init_axiom)
              except:
                  continue

              if init_axiom.rule not in bad_init_axiom:
                  break
                                    

        
        all_tactics.extend(init_axiom_tactics)
        init_state = state

        decl_name = "Trigo_data_" + str(count) + "_" + init_axiom.rule   #init_state2decl[init_state]
        # if decl_name.strip() != "Trigo_3_256_JROG":#"Trigo_1_89_VSEE":  "Trigo_0_24_FUOI"
        #    continue

        name_space = "real"
        print("init_output_state:{}".format(lean_output))
        print("decl_name:{}".format(decl_name))
        print("state:{}".format(state))
        print("====count:{}".format(count))
        #"suffices: {}".format(get_nonzero  ≠ 0)
        
        
         
        state_list = state.split("=")
        # state_list[0] = sympify(state_list[0])
        # state_list[1] = sympify(state_list[1])

        state_list_old = None
        #print("state_list:{}".format(state_list))
        tactic_list = []
        tactic_list_without_align = []
        alignment_tactic_list = []

        last_state = init_state#None
        last_state_old = None
        #tactic_converter_list = [cos_add_int_mul_two_pi_add_pi()] #,tactic_converter_list[j]
        prove_step_num = 0

        
        #problem_conditions_all = []
        prove_rules = []
        step_flag = False
        
        #['tan(X)=-1/tan(pi*K + X + pi/2)', 'tan(X - Y)=(tan(X) - tan(Y))/(tan(X)*tan(Y) + 1)', 'tan(X/2)=sin(X)/(cos(X) + 1)']
        bad_data_record = dict()
        all_tactics_record = []
        record_rules = []

         
        test_rule_list = []#["tan(X)=1/tan(pi*K - X + pi/2)", "tan(2*X)=2*tan(X)/(1 - tan(X)**2)", "tan(X/2)=sin(X)/(1+ cos(X))"]#["tan(2*X)=2*tan(X)/(1 - tan(X)**2)", "tan(X - Y)=(tan(X) - tan(Y))/(1 + tan(X)*tan(Y))", "tan(X/2)=sin(X)/(1+ cos(X))"]#["sin(2*X)=2*sin(X)*cos(X)", "sin(Y)*cos(X)=-sin(X - Y)/2 + sin(X + Y)/2", "cos(X)=cos(2*pi*K + X)"]#["sin(X - Y)=sin(X)*cos(Y) - sin(Y)*cos(X)", "sin(X)*cos(Y)=sin(X - Y)/2 + sin(X + Y)/2", "sin(X)=sin(2*pi*K + X)"]#['tan(X)=sin(X)/cos(X)', 'cos(3*X)=4*cos(X)**3 - 3*cos(X)', 'cos(X)=sin(2*X)/(2*sin(X))']#["tan(X)=sin(X)/cos(X)", "cos(3*X)=4*cos(X)**3 - 3*cos(X)", "cos(X)=sin(2*X)/(2*sin(X))"]#['cos(X + Y)=-sin(X)*sin(Y) + cos(X)*cos(Y)', 'sin(2*X)=2*sin(X)*cos(X)', 'sin(Y)*cos(X)=-sin(X - Y)/2 + sin(X + Y)/2']#['cos(X)=-sin(X + pi*(2*K + 1) + pi/2)', 'tan(X/2)=(1 - cos(X))/sin(X)']#['sin(X) + sin(Y)=2*sin(X/2 + Y/2)*cos(X/2 - Y/2)', 'cos(2*X)=2*cos(X)**2 - 1']#['sin(X) - sin(Y)=2*sin(X/2 - Y/2)*cos(X/2 + Y/2)']#['tan(2*X)=2*tan(X)/(1 - tan(X)**2)']#['tan(X) + tan(Y)=(-tan(X)*tan(Y) + 1)*tan(X + Y)', 'tan(X)*tan(Y)=(tan(X) - tan(Y))/tan(X - Y) - 1']#['cos(X + Y)=-sin(X)*sin(Y) + cos(X)*cos(Y)', 'cos(2*X)=2*cos(X)**2 - 1', "sin(X)**2 = 1 - cos(X)**2", "sin(X - Y)=sin(X)*cos(Y) - sin(Y)*cos(X)"]#['tan(X) + tan(Y)=(-tan(X)*tan(Y) + 1)*tan(X + Y)', 'tan(X)*tan(Y)=(tan(X) - tan(Y))/tan(X - Y) - 1'] #['tan(X - Y)=(tan(X) - tan(Y))/(tan(X)*tan(Y) + 1)', 'tan(X) - tan(Y)=sin(X - Y)/(cos(X)*cos(Y))']#['sin(X)=sin(-X + pi*(2*K + 1))', 'sin(3*X)=-4*sin(X)**3 + 3*sin(X)']#['sin(X)=cos(2*pi*K - X + pi/2)', 'sin(X + Y)=sin(X)*cos(Y) + sin(Y)*cos(X)']

        test = []
        for rule in test_rule_list:
            test.append(rule2name[rule])
        #getattr(a,'__name__')
       
        #test = [tan_div_two_2()]#[tan_sub(), tan_div_two_2()]#[tan_two_mul(), tan_two_mul(), tan_eq_sin_div_cos()]   [tan_two_mul(), tan_two_mul(), tan_sub()]  两个负号  [tan_sub(), tan_neg()] 除号 [tan_sub(),tan_eq_sin_div_cos(), cos_add_pi_div_two_add_pi()]
        conditions_sets = set()
 

        for k in range(0, 200): 
            if step_flag==True:
                continue
            #denominators_parsed = []
            sympy_state_problem_conditions = []
            problem_conditions = []

            axiom = random.choice(tactic_converter_list)#tan_add_pi_div_two()#random.choice(tactic_converter_list)#sin_mul_cos()#random.choice(tactic_converter_list)#sin_sub_sin() #tan_add_tan()#random.choice(tactic_converter_list)#sin_add_sin()#sin_mul_cos()#random.choice(tactic_converter_list)#tactic_converter_list[j]#random.choice(tactic_converter_list)#sin_eq_sin_two_mul()#sin_add_sin()#random.choice(tactic_converter_list)#sin_mul_cos()#random.choice(tactic_converter_list)#sin_add_int_mul_two_pi_add_pi()#random.choice(tactic_converter_list) #sin_mul_cos()
            
            expr_list = (axiom.rule).split("=")
            if axiom.rule=="A=X" or axiom.rule=="Abs(X)=-X" or axiom.rule=="ABC" :
                continue
            
            has_nonzero = axiom.has_nonzero
            flag = False
            substitution_dict = None
            new_state = None
            
            state = str(state_list[0]) + "=" + str(state_list[1])
            #print("=========================here1111111")
            for i, formula in enumerate(state_list):
                for j, expr in enumerate(expr_list): 
                    #expr = expr_list[0]
                    if j == 1:
                       continue

                    if flag == True:
                       continue
                    
                    
                    result = bottom_up_rule_match(sympify(formula,evaluate = False), sympify(expr,evaluate = False))
                    print("============result:{}".format(result))
                   
                    if len(result)!=0:
                        print("===============================================result_match")
                                            
                        print("axiom.rule:{}".format(axiom.rule))
                        print("state:{}".format(state))
                        substitution_expr = expr_list[1-j]#expr_list[1]#expr_list[1-j]

                        print("formula:{}".format(formula))
                        print("expr:{}".format(expr))
                        print("result:{}".format(result))
                        
                        #print("result[0]:{}".format(result[0]))
                        #print("substitution:{}".format(substitution))
                        # 完成了替换在这里
                        state_list_old = copy.deepcopy(state_list)
                        result_old = copy.deepcopy(result)
                        substitution_dict, expr_with_brackets, expr_olds = formula_substitution(state_list, result, substitution_expr, expr, i, axiom.rule)
                        #if "coef" in result[0].keys():
                        
                        #print("substitution_dict:{}".format(substitution_dict.keys()))
                        
                        new_state_temp = substitution_dict["new_state"]
                        if new_state_temp!= None:
                           new_state_temps = new_state_temp.split("=")
                        if new_state_temp != None and ("Abs" not in new_state_temp) and (new_state_temps[0].replace(" ","")!=new_state_temps[1].replace(" ","")):
                            new_state = new_state_temp
                            flag = True
                        else:
                            print("match error============================================")
                            state_list = copy.deepcopy(state_list_old)
                            result = copy.deepcopy(result_old)

            
            if flag == True:
                print("prove_step_num=======================================================================================================================000")
                print("substitution_dict[left]:{}".format(substitution_dict["left"]))
                print("substitution_dict[right]:{}".format(substitution_dict["right"]))
                print("substitution_dict[left]:{}".format(type(substitution_dict["left"])))
                print("substitution_dict[right]:{}".format(type(substitution_dict["right"])))
                tactics = axiom.get_tactics(substitution_dict, substitution_dict["left"], substitution_dict["right"])

                if substitution_dict["i"] == 0:
                      tactics_forward = ["have : "+ str(substitution_dict["left"]) + "  =  " + str(substitution_dict["right"])+","] + ["{"] + tactics + ["},"] + ["conv {to_lhs, rw this,}"]
                else:
                      tactics_forward = ["have : "+ str(substitution_dict["left"]) + "  =  " + str(substitution_dict["right"])+","] + ["{"] + tactics + ["},"] + ["conv {to_rhs, rw this,}"]

                print("axiom in bracket_list:{}".format(axiom.rule in bracket_list))
                print("expr_with_brackets:{}".format(expr_with_brackets))
                print("expr_olds:{}".format(expr_olds))
                tactics_with_bracket_prove = []
                
                if axiom.rule in bracket_list and expr_olds != None:
                #if  expr_olds != None:
                   print("====================================expr_olds")
                   for expr_with_bracket, expr_old in zip(expr_with_brackets, expr_olds):
                       
                            print("======================================================start from here")
                            if substitution_dict["i"] == 0:
                                 tactics_with_bracket = ["have : "+ expr_old + "  =  " + expr_with_bracket + ","] + ["{"] + ["ring,"] + ["},"] + ["conv {to_lhs, rw this,}"]
                                 tactics_with_bracket_prove = tactics_with_bracket_prove + ["have : "+  expr_with_bracket  + "  =  " + expr_old  + ","] + ["{"] + ["ring,"] + ["},"] + ["conv {to_lhs, rw this,}"]
                            else:
                                 tactics_with_bracket = ["have : "+ expr_old + "  =  " + expr_with_bracket + ","] + ["{"] + ["ring,"] + ["},"] + ["conv {to_rhs, rw this,}"]
                                 tactics_with_bracket_prove = tactics_with_bracket_prove + ["have : "+  expr_with_bracket  + "  =  " + expr_old  + ","] + ["{"] + ["ring,"] + ["},"] + ["conv {to_rhs, rw this,}"]


                            tactics_forward = tactics_with_bracket + tactics_forward
                
                tactics_with_bracket_prove_len = len(tactics_with_bracket_prove)
                if has_nonzero:
                   non_zeros = axiom.get_nonzero(substitution_dict, None, None) 
                   non_zero_number = len(non_zeros)
                   print("non_zeros:{}".format(non_zeros))
                   for non_zero in non_zeros:
                        try:
                            expr = sympify(non_zero,evaluate = False)
                            if abs(float(expr))<1e-8: 
                               continue
                        except:
                             pass
                                                                             
                   tactics_forward = ["suffices: {}".format( process_const_replacement(ParsePairBrackets(non_zero)).replace("--", "- -").replace("/-", "/ -") ) + "≠ 0," for non_zero in non_zeros] + tactics_forward#["tactic.rotate_left {},".format(non_zero_number)] + tactics_forward
                   problem_conditions = [non_zero for non_zero in non_zeros]
                   print("=================problem_conditions:{}".format(problem_conditions))
                    
                
                #state = new_state
                print("============================================backward000")
                last_state_old = last_state
                last_state = new_state #state
                print("last_state_old:{}".format(last_state_old))
                print("last_state:{}".format(last_state))
                state_list_old = last_state_old.split("=")#state_list
                print("state_list_old:{}".format(state_list_old))
                state_list = new_state.split("=")#state.split("=")
                print("state_list:{}".format(state_list))
                lean_output_old = lean_output

                conditions_sets_old = copy.deepcopy(conditions_sets)
                print("substitution_dict:{}".format(substitution_dict))
                print("============================================backward111")

                lean_output, excute_tactics, excute_tactics_record = excute_lean_gym(leanserver, tactics_forward, lean_output, last_state, tactics_with_bracket_prove_len = tactics_with_bracket_prove_len)

                #error_message = lean_output["error"]
                if (lean_output == None) or (lean_output["error"] != None):
                   if lean_output!=None:
                      record_rules.append(axiom.rule)
                      bad_data_record["decl_name"] = decl_name 
                      bad_data_record["record_rules"] = record_rules 
                      all_bad_data.append(bad_data_record)
                      all_tactics_record.extend(excute_tactics_record)

                      print("error_message:{}".format(lean_output))
                      print("decl_name:{}".format(decl_name))
                      print("record_rules:{}".format(record_rules))
                      print("count:{}".format(count))
                      print("all_tactics_record:{}".format(all_tactics_record))
                      print("init_state:{}".format(init_state))
                      if "time" not  in  lean_output["error"]:
                         pass
                         #assert 1==0
                      
                   #prove_step_num = k#j
                  
                   last_state = last_state_old
                   state_list = state_list_old
                   lean_output = lean_output_old
                   continue
                
                if lean_output["tactic_state"] == "no goals":
                   #prove_step_num = k#j
                   print("no goals lean_output:{}".format(lean_output))
                   last_state = last_state_old
                   state_list = state_list_old
                   lean_output = lean_output_old
                   continue

                print("after excute_lean_gym lean_output:{}".format(lean_output))
                tactic_state = (lean_output["tactic_state"].split("⊢ "))[1]

                if "⁻¹" in tactic_state or "**(-2)" in last_state:
                   last_state = last_state_old
                   state_list = state_list_old
                   lean_output = lean_output_old
                   continue

                tactic_state = tactic_state.split("\n\n")[0]
                  
                print("tactics_forward:{}".format(tactics_forward))
                print("tactic_state:{}".format(tactic_state))
                print("last_state:{}".format(last_state))

                
                if substitution_dict["i"] == 0:
                   tactics_skip_sympy_state = ["have : "+ tactic_state.split("=")[substitution_dict["i"]] + "  =  " + last_state.split("=")[substitution_dict["i"]] + "," ] + ["{"] +["try {field_simp at *}", "try {repeat {left}}", "try {ring}" ] + ["},"] + ["conv {to_lhs, rw this,}"]
                elif substitution_dict["i"] == 1:
                   tactics_skip_sympy_state = ["have : "+ tactic_state.split("=")[substitution_dict["i"]] + "  =  " + last_state.split("=")[substitution_dict["i"]] + "," ] + ["{"] +["try {field_simp at *}", "try {repeat {left}}", "try {ring}" ] + ["},"] + ["conv {to_rhs, rw this,}"]
                

                state1 = tactic_state.split("=")[substitution_dict["i"]].replace("cos x","cos(x)").replace("sin x","sin(x)").replace("cos y","cos(y)").replace("sin y","sin(y)").replace("sqrt 3","sqrt(3)").replace("sqrt 2","sqrt(2)").replace("sin pi","sin(pi)").replace("cos pi","cos(pi)").replace("tan x","tan(x)").replace("tan y","tan(y)").replace(" ","").replace("\n","")
                state2 = last_state.split("=")[substitution_dict["i"]].replace("cos x","cos(x)").replace("sin x","sin(x)").replace("cos y","cos(y)").replace("sin y","sin(y)").replace("sqrt 3","sqrt(3)").replace("sqrt 2","sqrt(2)").replace("sin pi","sin(pi)").replace("cos pi","cos(pi)").replace("tan x","tan(x)").replace("tan y","tan(y)").replace(" ","").replace("\n","")
                print("==state1:{}".format(state1))
                print("==state2:{}".format(state2))
                conditions1 = Get_Denominators(state1)
                conditions2 = Get_Denominators(state2)

                for condition in conditions1 + conditions2:
                    condition = (condition.replace(" ","")).strip()
                    if condition not in conditions_sets:
                        sympy_state_problem_conditions.append(condition)
                        conditions_sets.add(condition)
                       
                # sympy_state_problem_conditions.extend(conditions1)
                # sympy_state_problem_conditions.extend(conditions2)
            #  lean_states = get_lean_gym_state(leanserver, tactic_state, last_state, lean_output)
                #sympy_state_problem_conditions = get_denominator_from_lean_gym([tactic_state.split("=")[substitution_dict["i"]],  last_state.split("=")[substitution_dict["i"]]])
                
                print("=======================================================================expr1:{}".format(tactic_state.split("=")[substitution_dict["i"]].replace(" ","").replace("\n","")))
                print("=======================================================================expr2:{}".format(last_state.split("=")[substitution_dict["i"]].replace(" ","").replace("\n","")))
                print("=======================================================================sympy_state_problem_conditions0:{}".format(sympy_state_problem_conditions))
                sympy_state_problem_conditions = list(set(sympy_state_problem_conditions))
                
                if len(sympy_state_problem_conditions)>0:
                   tactics_suffices = ["suffices: {}".format(process_const_replacement(non_zero)).replace("--", "- -").replace("/-", "/ -") + "≠ 0," for non_zero in sympy_state_problem_conditions] #["tactic.rotate_left {},".format(non_zero_number)] + tactics_forward
                   tactics_skip_sympy_state = tactics_suffices + tactics_skip_sympy_state


                print("0=================lean_output_state:{}".format(lean_output))
                if "0 -" in lean_output["tactic_state"]:
                      record_rules.append(axiom.rule)
                                           
                      bad_data_record["decl_name"] = decl_name + "_0"
                      bad_data_record["record_rules"] = record_rules 
                      all_bad_data.append(bad_data_record)
                      print("decl_name:{}".format(decl_name))
                      print("record_rules:{}".format(record_rules))
                      print("count:{}".format(count))
                      print("tactics_forward:{}".format(tactics_forward+tactics_skip_sympy_state))
                      #assert 1==0

                print("=================check tactics_skip_sympy_state:{}".format(tactics_skip_sympy_state))
                lean_output, excute_tactics_alignment, excute_tactics_alignment_record = excute_lean_gym(leanserver, tactics_skip_sympy_state, lean_output, last_state)

                #print("1=================lean_output_state:{}".format(lean_output))
                #error_message = lean_output["error"]
                if (lean_output==None) or (lean_output["error"] != None):
                   print("2=================lean_output_state:{}".format(lean_output))
                   print("error_message:{}".format(lean_output))
                   if lean_output!=None:
                      record_rules.append(axiom.rule)
                      bad_data_record["decl_name"] = decl_name 
                      bad_data_record["record_rules"] = record_rules 
                      all_bad_data.append(bad_data_record)
                      print("decl_name:{}".format(decl_name))
                      print("record_rules:{}".format(record_rules))
                      print("count:{}".format(count))
                      print("tactics_forward:{}".format(tactics_forward+tactics_skip_sympy_state))

                      if "time" not  in  lean_output["error"]:
                         #assert 1==0
                         pass
                   
                   last_state = last_state_old
                   state_list = state_list_old
                   lean_output = lean_output_old
                   
                   conditions_sets = copy.deepcopy(conditions_sets_old)
                   print("3=================lean_output_state:{}".format(lean_output))
                   continue
                
                # 在这里只是用一边证明
                if substitution_dict["i"] == 0:
                   tactics_skip_sympy_state_prove = ["have : "+ tactic_state.split("=")[substitution_dict["i"]]  + "  =  " + last_state.split("=")[substitution_dict["i"]] + "," ] + ["{"] + excute_tactics_alignment + ["},"] + ["conv {to_lhs, rw ← this,}"]#["rw this,"]
                else:
                   tactics_skip_sympy_state_prove = ["have : "+ tactic_state.split("=")[substitution_dict["i"]]   + "  =  " + last_state.split("=")[substitution_dict["i"]] + "," ] + ["{"] + excute_tactics_alignment + ["},"] + ["conv {to_rhs, rw ← this,}"]#["rw this,"]
                   
                tactics_prove = get_prove_tactic(axiom.rule, excute_tactics, substitution_dict["i"])
                tactics_prove_without_align = tactics_prove
                print("===tactics_skip_sympy_state_prove:{}".format(tactics_skip_sympy_state_prove))
                print("===tactics_forward:{}".format(tactics_forward))
                print("===excute_tactics:{}".format(excute_tactics))
                print("===tactics_prove:{}".format(tactics_prove))
                print("===tactics_with_bracket_prove:{}".format(tactics_with_bracket_prove))

                tactics_prove =   tactics_skip_sympy_state_prove  + tactics_prove + tactics_with_bracket_prove
                        
                prove_rules.append(axiom.rule)
                print("extend excute_tactics:{}".format(excute_tactics))
                print("excute_tactics_alignment:{}".format(excute_tactics_alignment))
                all_tactics_record.extend(excute_tactics_record)
                all_tactics_record.extend(excute_tactics_alignment_record)
                print("has_nonzero:{}".format(has_nonzero))
                #print("sympy lean_output:{}".format(lean_output))

            
                tactic_list = tactics_prove + tactic_list#.extend(tactics)
                tactic_list_without_align = tactics_prove_without_align + tactic_list_without_align
              

                problem_conditions_all.extend(problem_conditions) 
                print("=======================================================================problem_conditions1:{}".format(problem_conditions))
                print("=======================================================================sympy_state_problem_conditions1:{}".format(sympy_state_problem_conditions))
                problem_conditions_all.extend(sympy_state_problem_conditions)
                alignment_tactic_list.append(tactics_skip_sympy_state_prove)
                problem_conditions = []
                sympy_state_problem_conditions = []
                prove_step_num += 1

                record_rules.append(axiom.rule)
                if prove_step_num ==prove_count:
                   print("prove_step_num=======================================================================================================================")
                   
                   step_flag = True




            #decl2prove_step_num[decl] = j
        #decl = init_state2decl[init_state]

        all_tactics = tactic_list + init_axiom_tactics#decl2data[decl]
        
        data_dict = dict()
        

        all_tactics = process_all_tactics(all_tactics)     # tactic_list_without_align
        # data_dict["proves_tactics_without_align"] = tactic_list_without_align#all_tactics
        # data_dict["proves_alignment_tactic"] = alignment_tactic_list#all_tactics
        data_dict["proves_tactics"] = all_tactics
        data_dict["last_state"] = last_state
        data_dict["prove_step_num"] = prove_step_num#j
        data_dict["init_state"] = init_state
        data_dict["decl_name"] = decl_name
        data_dict["problem_conditions"] = problem_conditions_all
        data_dict["prove_rules"] = prove_rules
        #data_dict["all_bad_data"] = all_bad_data
        all_data_list.append(data_dict)
        leanserver.clear_search(lean_output["search_id"])

        #if count % 1000 == 0:
    with open("generated_data/step"+ str(prove_count) +"/from_rule_data_step" + str(prove_count) + "_" + "number_generalization_2" + ".json", 'w') as f:
        f.write(json.dumps(all_data_list))



                    