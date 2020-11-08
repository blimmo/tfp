import itertools
import math
from functools import reduce
import operator

import aiger
import aiger_sat


def at_most_one(literals):
    return reduce(operator.and_, (~a | ~b for a, b in itertools.combinations(literals, 2)))

def at_least_one(literals):
    return reduce(operator.or_, literals)

def exactly_one(literals):
    literals = list(literals)
    return at_most_one(literals) & at_least_one(literals)

def all_(literals):
    return reduce(operator.and_, literals)


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
    def distinct2(s):
        return list(itertools.permutations(s, 2))

    l_vars = {
        (u, v): aiger.atom(f"L_{u}->{v}")
        for u, v in distinct2(afud)
        if v != v_star
    }
    psi_vars = {
        (u, i): aiger.atom(f"psi_{u}<={i}")
        for u in dummy
        for i in typesaf
    }
    chi_vars = {
        (u, b): aiger.atom(f"chi_{u}_{b}")
        for u in afud
        for b in range(D.ln + 1)
    }
    b_indices = list(range(math.floor(math.log2(D.ln))))
    length_vars = {
        (u, v, b): aiger.atom(f"len_{u}->{v}_{b}")
        for b in b_indices
        for u, v in distinct2(afud)
        if v != v_star
    }
    dist_vars = {
        (u, d): aiger.atom(f"dist_{u}_{d}")
        for u in afuddv
        for d in range(1, D.ln + 1)
    }
    # g vars

    realizable = aiger.atom(True)
    # validity
    for u in afuddv:
        # AtMostOneParent(u)
        realizable &= at_most_one(l_vars[v, u] for v in afud if v != u)
    for u in dummy:
        # ExactlyOneType(u)
        realizable &= exactly_one(psi_vars[u, i] for i in typesaf)
    for u in afud:
        # ExactlyOneSizeBit(u)
        realizable &= exactly_one(chi_vars[u, b] for b in range(D.ln + 1))
    realizable &= chi_vars[v_star, D.ln]
    for u in afuddv:
        # AtMostOneDist(u)
        realizable &= at_most_one(dist_vars[u, d] for d in range(1, D.ln + 1))
    for u in v_f:
        # AtLeastOneDist(u)
        realizable &= at_least_one(dist_vars[u, d] for d in range(1, D.ln + 1))
    for u in v_f:
        realizable &= dist_vars[u, 1].implies(l_vars[v_star, u])
        for d in range(2, D.ln):
            # VerifyDist_d(u)
            realizable &= dist_vars[u, d].implies(at_least_one(
                l_vars[w, u] & dist_vars[w, d - 1]
                for w in afuddv if w != u
            ))
    reachable = {u: at_least_one(dist_vars[u, d] for d in range(1, D.ln)) for u in dummy}
    notleaf = {u: ~reachable[u] | at_least_one(l_vars[u, w] for w in afuddv if w != u) for u in dummy}
    isnode = {u: aiger.atom(True) if u in a_f else reachable[u] for u in afud}
    isarc = {
        (u, v): isnode[u] & isnode[v] & l_vars[u, v] if v != v_star else aiger.atom(False)
        for u, v in distinct2(afud)
    }
    # for u, v in itertools.permutations(afud, 2):
    def beats(u, v):
        if u in a_f and v in a_f:
            if v in D[u]:
                return aiger.atom(True)
            else:
                return aiger.atom(False)
        if u in a_f:
            return at_least_one(psi_vars[v, i] for i in typesaf if i > tau[u])
        if v in a_f:
            return at_least_one(psi_vars[u, i] for i in typesaf if i > tau[v])
        return at_least_one(psi_vars[u, i] & psi_vars[v, j]
                            for i, j in itertools.combinations(reversed(typesaf), 2))

    ifarcthenvalid = {(u, v): isarc[u, v].implies(beats(u, v)) for u, v in distinct2(afud)}
    inclosure = {u: isnode[u] & at_least_one(l_vars[u, p] & l_vars[u, q]
                                             for p, q in itertools.combinations(afuddv, 2)
                                             if p != u and q != u) for u in dummy}
    childofclosure = {u: isnode[u] & ~inclosure[u] for u in dummy}
    nodeg2consecdum = {
        (u, v): (isarc[u, v] & childofclosure[u]).implies(childofclosure[v])
        for u, v in distinct2(dummy)
    }


    s = aiger_sat.SolverWrapper()
    s.add_expr(realizable)
    print(s.get_model())
    return s.is_sat()

def solve(G):
    return {v for v in (1,) if solve_one(G, v)}

# if __name__ == "__main__":
#     solve_one(G)
