import itertools
import math

from pysat.solvers import Glucose4 as SAT


class Variables:
    def __init__(self):
        self.k = 1
        self.vars = {}

    def add(self, index):
        self.vars[index] = self.k
        self.k += 1

    def __getitem__(self, index):
        return self.vars[index]


def solve_one(D, v_star):
    v_f = frozenset(sum(D.feedback, start=()))
    a_f = v_f.union((v_star,))

    tau = {}
    num = [0]
    for v in D.order:
        if v in a_f:
            tau[v] = len(num) - 0.5
            num.append(0)
        else:
            tau[v] = len(num) - 1
            num[-1] += 1
    num = tuple(num)
    typesaf = tuple(range(len(num)))
    types = tuple(i / 2 for i in range(2 * len(a_f) + 1))

    l = 4 * (2 * len(a_f) + 1) - len(a_f)
    l = 6
    dummy = {-i for i in range(1, l + 1)}
    afud = a_f.union(dummy)
    afuddv = afud.difference({v_star})

    vars = Variables()

    # l_vars
    for u, v in itertools.permutations(afud, 2):
        if v != v_star:
            vars.add(("L", u, v))
    # psi_vars
    for u in dummy:
        for i in typesaf:
            vars.add(("psi", u, i))
    # chi_vars
    for u in afud:
        for b in range(D.ln + 1):
            vars.add(("chi", u, b))
    # length_vars
    for u, v in itertools.combinations(afud, 2):
        if v != v_star:
            for b in range(math.floor(math.log2(D.ln))):
                vars.add(("len", u, v, b))
    # dist_vars
    for u in afuddv:
        for d in range(1, D.ln):
            vars.add(("dist", u, d))
    # g vars

    realizable = SAT()

    def at_most_one(literals):
        return tuple((-a, -b) for a, b in itertools.combinations(literals, 2))

    def exactly_one(literals):
        return at_most_one(literals) + (literals,)

    # validity
    for u in afuddv:
        # AtMostOneParent(u)
        realizable.append_formula(at_most_one(tuple(vars["L", v, u] for v in afud if v != u)))
    for u in dummy:
        # ExactlyOneType(u)
        realizable.append_formula(exactly_one(tuple(vars["psi", u, i] for i in typesaf)))
    for u in afud:
        # ExactlyOneSizeBit(u)
        realizable.append_formula(exactly_one(tuple(vars["chi", u, b] for b in range(D.ln + 1))))
        realizable.add_clause((vars["chi", v_star, D.ln],))
    for u in afuddv:
        # AtMostOneDist(u)
        realizable.append_formula(at_most_one(tuple(vars["dist", u, d] for d in range(1, D.ln))))
    for u in v_f:
        # AtLeastOneDist(u)
        realizable.add_clause(tuple(vars["dist", u, d] for d in range(1, D.ln)))
    for u in v_f:
        realizable.add_clause((-vars["dist", u, 1], vars["L", v_star, u]))
        # for d in range(2, D.ln):
            # VerifyDist_d(u)
            # realizable.add_clause((vars["dist", u, d],))
            # pass
    # for u in dummy:

    def reachable(u):
        return tuple(vars["dist", u, d] for d in range(1, D.ln))



    def beats(u, v):
        if u in a_f and v in a_f:
            if v in D[u]:
                return ()
            else:
                return False  # uh that's not a clause
        if u in a_f:
            return tuple(vars["psi", u, i] for i in typesaf if i > tau[u])
        if v in a_f:
            return tuple(vars["psi", v, i] for i in typesaf if i > tau[v])
        # return tuple(itertools.combinations(vars["psi", u,for i, j in itertools.combinations(typesaf, 2)

    realizable.solve()
    m = realizable.get_model()
    for k, v in vars.vars.items():
        if v in m:
            print(k)
        elif -v in m:
            print(f"¬{k}")
        else:
            print("oops")

def solve(G):
    return {v for v in (1,) if solve_one(G, v)}

# if __name__ == "__main__":
#     solve_one(G)
