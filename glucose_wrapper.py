from sympy.assumptions.cnf import EncodedCNF
from pysat.solvers import Glucose3

def glucose_satisfiable(expr):
    if not isinstance(expr, EncodedCNF):
        exprs = EncodedCNF()
        exprs.add_prop(expr)
        expr = exprs

    s = Glucose3(bootstrap_with=expr.data)
    result = s.solve()
    if not result:
        return result
    return {expr.symbols[abs(lit) - 1]: lit > 0 for lit in s.get_model()}
