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
    return reduce(operator.and_, literals, aiger.atom(True))

def distinct2(s):
    return list(itertools.permutations(s, 2))

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
    dummy = {-i for i in range(1, l + 1)}
    cond = Conditions.make(D, v_star, v_f, a_f, dummy, typesaf, tau)


class Conditions:
    def __init__(self, D=None, ln=None, v_star=None, v_f=None, a_f=None, dummy=None,
                 typesaf=None, tau=None, afud=None, afuddv=None):
        self.D = D
        self.ln = ln
        self.v_star = v_star
        self.v_f = v_f
        self.a_f = a_f
        self.dummy = dummy
        self.typesaf = typesaf
        self.tau = tau
        self.afud = afud
        self.afuddv = afuddv

    @classmethod
    def make(cls, D, v_star, v_f, a_f, dummy, typesaf, tau):
        afud = a_f.union(dummy)
        ins = cls(D, D.ln, v_star, v_f, a_f, dummy, typesaf, tau, afud,
                  afud.difference({v_star}))
        ins.gen_l_vars()
        ins.gen_psi_vars()
        ins.gen_chi_vars()
        ins.gen_length_vars()
        ins.gen_dist_vars()
        return ins

    def gen_l_vars(self):
        self.l_vars = ret = {
            (u, v): aiger.atom(f"L_{u}->{v}")
            for u, v in distinct2(self.afud)
            if v != self.v_star
        }
        return ret

    def gen_psi_vars(self):
        self.psi_vars = ret = {
            (u, i): aiger.atom(f"psi_{u}<={i}")
            for u in self.dummy
            for i in self.typesaf
        }
        return ret

    def gen_chi_vars(self):
        self.chi_b_indices = list(range(self.ln + 1))
        self.chi_vars = ret = {
            (u, b): aiger.atom(f"chi_{u}_{b}")
            for u in self.afud
            for b in self.chi_b_indices
        }
        return ret

    def gen_length_vars(self):
        self.length_b_indices = list(range(math.floor(math.log2(D.ln))))
        self.length_vars = ret = {
            (u, v, b): aiger.atom(f"len_{u}->{v}_{b}")
            for b in self.length_b_indices
            for u, v in distinct2(self.afud)
            if v != self.v_star
        }
        return ret

    def gen_dist_vars(self):
        self.dist_b_indices = list(range(1, self.ln + 1))
        self.dist_vars = ret = {
            (u, d): aiger.atom(f"dist_{u}_{d}")
            for u in self.afuddv
            for d in self.dist_b_indices
        }
        return ret

    def gen_same_bit_vars(self):
        """For LocCheckSize(Dec/Diff)"""
        self.samebitvars = {(u, v, b): aiger.atom(f"samebit_{u}_{v}_{b}")
                            for b in self.chi_b_indices for u, v in distinct2(self.afud)}
        samebitclauses = all_(all_(self.samebitvars[u, v, b] == ((self.chi_vars[u, b] & self.chi_vars[v, b])
                                                                 | (~self.chi_vars[u, b] & ~self.chi_vars[v, b]))
                                   for b in self.chi_b_indices)
                              for u, v in distinct2(self.afud))
        return samebitclauses

    # g vars

    # validity
    def atmostoneparent(self, u):
        assert u in self.afuddv
        return at_most_one(self.l_vars[v, u] for v in self.afud if v != u)

    def exactlyonetype(self, u):
        assert u in self.dummy
        return exactly_one(self.psi_vars[u, i] for i in self.typesaf)

    def exactlyonesizebit(self, u):
        assert u in self.afud
        return exactly_one(self.chi_vars[u, b] for b in self.chi_b_indices)

    def atmostonedist(self, u):
        assert u in self.afuddv
        return at_most_one(self.dist_vars[u, d] for d in self.dist_b_indices)

    def atleastonedist(self, u):
        assert u in self.v_f
        return at_least_one(self.dist_vars[u, d] for d in self.dist_b_indices)

    def verify_dist(self, u, d):
        # for u in v_f:
        # VerifyDist_d(u)
        if d == 1:
            return self.dist_vars[u, d].implies(self.l_vars[self.v_star, u])
        return self.dist_vars[u, d].implies(at_least_one(
            self.l_vars[w, u] & self.dist_vars[w, d - 1]
            for w in self.afuddv if w != u
        ))

    def reachable(self, u):
        assert u in self.dummy
        return at_least_one(self.dist_vars[u, d] for d in self.dist_b_indices)

    def notleaf(self, u):
        assert u in self.dummy
        return ~self.reachable(u) | at_least_one(self.l_vars[u, w] for w in self.afuddv if w != u)

    def isnode(self, u):
        assert u in self.afud
        return aiger.atom(True) if u in self.a_f else self.reachable(u)

    def isarc(self, u, v):
        assert u in self.afud and v in self.afud and u != v
        return self.isnode(u) & self.isnode(v) & self.l_vars[u, v] if v != self.v_star else aiger.atom(False)

    # for u, v in itertools.permutations(afud, 2):
    def beats(self, u, v):
        if u in self.a_f and v in self.a_f:
            if v in self.D[u]:
                return aiger.atom(True)
            else:
                return aiger.atom(False)
        if u in self.a_f:
            return at_least_one(self.psi_vars[v, i] for i in self.typesaf if i > self.tau[u])
        if v in self.a_f:
            return at_least_one(self.psi_vars[u, i] for i in self.typesaf if i > self.tau[v])
        return at_least_one(self.psi_vars[u, i] & self.psi_vars[v, j]
                            for i, j in itertools.combinations(reversed(self.typesaf), 2))

    def ifarcthenvalid(self, u, v):
        assert u in self.afud and v in self.afud and u != v
        return self.isarc(u, v).implies(self.beats(u, v))

    def inclosure(self, u):
        assert u in self.dummy
        return self.isnode(u) & at_least_one(self.l_vars[u, p] & self.l_vars[u, q]
                                             for p, q in itertools.combinations(self.afuddv, 2)
                                             if p != u and q != u)

    def childofclosure(self, u):
        assert u in self.dummy
        return self.isnode(u) & ~self.inclosure(u)

    def nodeg2consecdum(self, u, v):
        assert u in self.dummy and v in self.dummy and u != v
        return (self.isarc(u, v) & self.childofclosure(u)).implies(self.childofclosure(v))

    def locchecklensensible(self, u, v):
        # for u, v in distinct2(afud) if v != v_star  # possibly should just be false for v_star
        assert u in self.afud and v in self.afud and u != v
        return (self.isarc(u, v) & (aiger.atom(True) if u in self.a_f else self.inclosure(u))
                ).implies(all_(~self.length_vars[u, v, b] for b in self.length_b_indices))

    def locchecksizedec(self, u, v):
        assert u in self.afud and v in self.afud and u != v
        return self.isarc(u, v).implies(
            at_least_one(all_(self.samebitvars[u, v, i] for i in self.chi_b_indices if i > b)  # largest condition
                         & ~self.samebitvars[u, v, b] & self.chi_vars[u, b] & ~self.chi_vars[v, b]
                         for b in self.chi_b_indices)
        )

    def locchecksizediff(self, u, v, w):
        assert u in self.afud and v in self.afud and w in self.afud
        return (self.isarc(u, v) & self.isarc(u, w)).implies(
            ~all_(self.samebitvars[v, w, b] for b in self.chi_b_indices)
        )

    # realizable = aiger.atom(True)
    # realizable &= chi_vars[v_star, D.ln]
    #
    # s = aiger_sat.SolverWrapper()
    # s.add_expr(realizable)
    # m = s.get_model()
    # print(m)
    # print(*afud)
    # for b in chi_b_indices:
    #     print(*(1 if m[f"chi_{u}_{b}"] else 0 for u in afud))
    # return s.is_sat()

def solve(G):
    return {v for v in (1,) if solve_one(G, v)}

# if __name__ == "__main__":
#     solve_one(G)
