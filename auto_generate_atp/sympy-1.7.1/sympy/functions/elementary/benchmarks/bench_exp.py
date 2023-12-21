from sympy import exp, symbols

x, y = symbols('x,y')

e = exp(2*x)
q = exp(3*x)


def timeit_exp_subs():
    e.subs(q, y)
