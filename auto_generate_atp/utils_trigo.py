import os
ROOTDIR = os.path.abspath(os.path.join(__file__, os.path.pardir, os.path.pardir))
from lean_server import LeanServer
from sympy import *
sin = Function('sin')
cos = Function('cos')
tan = Function('tan')

'''
open real
open_locale real

lemma basic_truth_with_x (x : ℝ) : 0=0:=
begin
  refl,
end

lemma basic_truth : 0=0:=
begin
  refl,
end
'''


# class FreeServer:
#     def __init__(self):
#         self._server = LeanServer()
#         self._last_search_id = None
#
#     def get_server_with_state(self, have_input):
#         ''' get a server with left = right as the state'''
#         _server = self._server
#         if self._last_search_id is not None:
#             _server.clear_search(self._last_search_id)
#         if "x" in have_input:
#             output = _server.init_search("basic_truth_with_x", "real")
#         else:
#             output = _server.init_search("basic_truth", "real")
#         self._last_search_id = output["search_id"]
#         _server.run_tac(self._last_search_id, 0, "intros")
#         suffices_goal = have_input.replace("have", "suffices")
#         output = _server.run_tac(self._last_search_id, 1, f"suffices : {suffices_goal}")
#         output = _server.run_tac(self._last_search_id, 2, "refl")
#         output = _server.run_tac(self._last_search_id, 3, "intros")
#         return output, self._server


class FreeServer:
    def __init__(self):
        self._server = LeanServer()
        self._last_search_id = None


    def get_server_with_state(self, left, right, denoms=None, pos_value=None, neg_value=None):
        ''' get a server with left = right as the state'''
        _server = self._server
        if self._last_search_id is not None:
            _server.clear_search(self._last_search_id)

        output = _server.init_search("basic_truth", "real")
        self._last_search_id = output["search_id"]
        _server.run_tac(self._last_search_id, 0, "intros")
        suffices_goal = f"{left} = {right}"
        if denoms:
            for d in denoms:
                suffices_goal = f"({d} ≠ 0) → " + suffices_goal
        if pos_value is not None:

            if isinstance(pos_value, list):
                for pos_in_abs in pos_value:
                    suffices_goal = f"({pos_in_abs}≥0) → " + suffices_goal
            else:
                pos_in_abs = left[4:-1]
                suffices_goal = f"({pos_in_abs}≥0) → " + suffices_goal
        if neg_value is not None:
            if isinstance(neg_value, list):
                for neg_in_abs in neg_value:
                    suffices_goal = f"({neg_in_abs}≤0) → " + suffices_goal
            else:
                neg_in_abs = left[4:-1]
                suffices_goal = f"({neg_in_abs}≤0) → " + suffices_goal
        output = _server.run_tac(self._last_search_id, 1, f"suffices : {suffices_goal}")
        output = _server.run_tac(self._last_search_id, 2, "refl")
        output = _server.run_tac(self._last_search_id, 3, "intros")
        return output, self._server

def _find_denom(expr):
    denominators = []
    if expr.is_Add or expr.is_Mul:
        args = expr.args
        for arg in args:
            denominators += _find_denom(arg)
    elif expr.is_Pow:
        if expr.args[1] < 0:
            dem = expr.args[0]
            if dem.is_Mul:
                for arg in dem.args:
                    denominators.append(arg)
            else:
                denominators.append(dem)
        else:
            denominators += _find_denom(expr.args[0])
    else:
        return []

    return denominators

def trig2mytrig(rule):
    rule = rule.replace("sin", "myasin")
    rule = rule.replace("cos", "mybcos")
    rule = rule.replace("tan", "myctan")
    return rule

def mytrig2trig(rule):
    rule = rule.replace("myasin", "sin")
    rule = rule.replace("mybcos", "cos")
    rule = rule.replace("myctan", "tan")
    return rule

def get_denominators(expr):
    with evaluate(False):
         expr = trig2mytrig(expr)
         expr = parse_expr(expr, evaluate=False)
         denoms = _find_denom(expr)
         denoms = [mytrig2trig(str(x)) for x in denoms]
    # demons = [str(x) for x in denoms]
    return  denoms

if __name__ == "__main__":
    x, y = symbols('x y')
    rule = "-cos(pi/36)/sin(pi/36) + sin(pi/36)/cos(pi/36) = (-cos(pi/36)**2 + sin(pi/36)**2)/(sin(pi/36)*cos(pi/36))"
    rule_left, rule_right = rule.split("=")
    denoms = get_denominators(rule_left)
    server = FreeServer()
    output, server = server.get_server_with_state(rule_left, rule_right, denoms)
    print(output)
    output = server.run_tac(output["search_id"], output["tactic_state_id"], "try {field_simp}")
    print(output)
    output = server.run_tac(output["search_id"], output["tactic_state_id"], "try {ring_exp}")
    print(output)

    # server = FreeServer()
    # output, _ = server.get_server_with_state("sin(x)", "sin(x + 2*pi)")
    # print(output)

