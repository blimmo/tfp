from sympy.assumptions.cnf import EncodedCNF, CNF
from pysat.solvers import Glucose4 as Solver

def glucose_satisfiable(exprs):
    cnf = CNF()
    for expr in exprs:
        cnf.add(expr)
    encoded = EncodedCNF()
    encoded.from_cnf(cnf)

    with Solver() as s:
        for rclause in encoded.data:
            clause = [literal for literal in rclause if literal != 0]
            if len(clause) == 0:
                return False
            s.add_clause(clause)
        result = s.solve()
        if not result:
            return result
        return {encoded.symbols[abs(lit) - 1]: lit > 0 for lit in s.get_model()}
