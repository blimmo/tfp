import itertools
import math
import operator
from functools import reduce

import aiger
import aiger_sat


def at_most_one(literals):
    return reduce(operator.and_, (~a | ~b for a, b in itertools.combinations(literals, 2)))

def at_least_one(literals):
    return reduce(operator.or_, literals, aiger.atom(False))

def exactly_one(literals):
    literals = list(literals)
    return at_most_one(literals) & at_least_one(literals)

def all_(literals):
    return reduce(operator.and_, literals, aiger.atom(True))

def distinct2(s):
    return list(itertools.permutations(s, 2))

def solve_one(graph, v_star):
    v_f = frozenset(sum(graph.feedback, start=()))
    a_f = v_f.union((v_star,))

    tau = {}
    num = [0]
    for v in graph.order:
        if v in a_f:
            tau[v] = len(num) - 0.5
            num.append(0)
        else:
            tau[v] = len(num) - 1
            num[-1] += 1
    num = tuple(num)
    naftypes = tuple(range(len(num)))
    types = tuple(i / 2 for i in range(2 * len(a_f) + 1))

    dummy_size = min(4 * (2 * len(graph.feedback) + 1), graph.n) - len(a_f)  # maybe 4 * len(a_f)?
    dummy = {-i for i in range(1, dummy_size + 1)}
    return Conditions.make(graph, v_star, v_f, a_f, dummy, naftypes, tau).solve() is not None


class Conditions:
    def __init__(self, graph=None, ln=None, v_star=None, v_f=None, a_f=None, dummy=None,
                 naftypes=None, tau=None, afud=None, afuddv=None):
        self.graph = graph
        self.ln = ln
        if ln is not None:
            self.ln_indices = list(range(ln + 1))
            self.lln = lln = math.ceil(math.log2(ln + 1))
            self.lln_indices = list(range(lln))
        self.v_star = v_star
        self.v_f = v_f
        self.a_f = a_f
        self.dummy = dummy
        self.naftypes = naftypes
        self.tau = tau
        self.afud = afud
        self.afuddv = afuddv
        self.afud_and_pairs = afud.union(itertools.product(afud, repeat=2))
        self.variable_clauses = aiger.atom(True)

    @classmethod
    def make(cls, graph, v_star, v_f, a_f, dummy, typesaf, tau):
        afud = a_f.union(dummy)
        ins = cls(graph, graph.ln, v_star, v_f, a_f, dummy, typesaf, tau, afud,
                  afud.difference({v_star}))
        print("l")
        ins.gen_l_vars()
        print("psi")
        ins.gen_psi_vars()
        print("chi")
        ins.gen_chi_vars()
        print("len")
        ins.gen_length_vars()
        print("dist")
        ins.gen_dist_vars()
        print("same bit")
        ins.gen_same_bit_vars()
        print("w")
        ins.gen_w_vars()
        print("y")
        ins.gen_y_vars()
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
            for i in self.naftypes
        }
        return ret

    def gen_chi_vars(self):
        self.chi_vars = ret = {
            (u, b): aiger.atom(f"chi_{u}_{b}")
            for u in self.afud
            for b in self.ln_indices
        }
        return ret

    def gen_length_vars(self):
        self.length_vars = ret = {
            (u, v, b): aiger.atom(f"len_{u}->{v}_{b}")
            for b in self.lln_indices
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
        self.variable_clauses &= all_(all_(self.verify_dist(u, d) for u in self.v_f) for d in self.dist_b_indices)
        return ret

    def gen_g_vars(self):
        self.g_vars = {
            (e, i, b): aiger.atom(f"g_{e}_{i}_{b}")
            for e in self.afud_and_pairs
            for i in self.naftypes
            for b in self.ln_indices
        }

    def gen_same_bit_vars(self):
        """For LocCheckSize(Dec/Diff)"""
        self.same_bit_vars = same_bit_vars = {(u, v, b): aiger.atom(f"samebit_{u}_{v}_{b}")
                                              for b in self.ln_indices for u, v in distinct2(self.afud)}
        self.variable_clauses &= all_(all_(same_bit_vars[u, v, b] == ((self.chi_vars[u, b] & self.chi_vars[v, b])
                                                                | (~self.chi_vars[u, b] & ~self.chi_vars[v, b]))
                                           for b in self.ln_indices)
                                      for u, v in distinct2(self.afud))
        return same_bit_vars

    def gen_w_vars(self):
        """For LocCheckPath. Represents chi"""
        self.w_vars = w_vars = {(v, b): aiger.atom(f"w_{v}_{b}")
                                for b in self.lln_indices for v in self.afud}
        self.variable_clauses &= all_(all_(self.chi_vars[v, b].implies(all_(
                                               w_vars[v, i] if ((b >> i) & 1) == 1 else ~w_vars[v, i]
                                               for i in self.lln_indices
                                           ))
                                           for b in self.ln_indices)
                                      for v in self.afud)
        return w_vars

    # noinspection PyTypeChecker
    def gen_y_vars(self):
        """For LocCheckPath. Represents chi + l"""
        self.y_vars = y_vars = {(u, v, b): aiger.atom(f"y_{u}_{v}_{b}")
                                for b in self.lln_indices + [self.lln]
                                for u, v in distinct2(self.afud)
                                if v != self.v_star}
        c_vars = {(u, v, b): aiger.atom(f"c_{u}_{v}_{b}")
                  for b in self.lln_indices[:-1]
                  for u, v in distinct2(self.afud)
                  if v != self.v_star}
        c_clauses = all_(
            (c_vars[u, v, 0] == (self.w_vars[v, 0] & self.length_vars[u, v, 0])) &
            all_(
                c_vars[u, v, b] == (
                    # at least 2
                    (self.w_vars[v, b] & self.length_vars[u, v, b]) |
                    (self.w_vars[v, b] & c_vars[u, v, b - 1]) |
                    (c_vars[u, v, b - 1] & self.length_vars[u, v, b])
                )
                for b in self.lln_indices[1:-1]
            )
            for u, v in distinct2(self.afud)
            if v != self.v_star
        )
        y_clauses = all_(
            (y_vars[u, v, 0] == (self.w_vars[v, 0] ^ self.length_vars[u, v, 0])) &
            all_(
                y_vars[u, v, b] == (
                    # exactly 1
                    (self.w_vars[v, b] ^ self.length_vars[u, v, b] ^ c_vars[u, v, b - 1]) |
                    # or exactly 3
                    (self.w_vars[v, b] & self.length_vars[u, v, b] & c_vars[u, v, b - 1])
                )
                for b in self.lln_indices[1:]
            ) &
            (y_vars[u, v, self.lln] == self.w_vars[v, self.lln - 1] & self.length_vars[u, v, self.lln - 1])
            for u, v in distinct2(self.afud)
            if v != self.v_star
        )
        self.variable_clauses &= c_clauses & y_clauses
        return y_vars

    # g vars

    # validity
    def at_most_one_parent(self, u):
        assert u in self.afuddv
        return at_most_one(self.l_vars[v, u] for v in self.afud if v != u)

    def exactly_one_type(self, u):
        assert u in self.dummy
        return exactly_one(self.psi_vars[u, i] for i in self.naftypes)

    def exactly_one_size_bit(self, u):
        assert u in self.afud
        return exactly_one(self.chi_vars[u, b] for b in self.ln_indices)

    def at_most_one_dist(self, u):
        assert u in self.afuddv
        return at_most_one(self.dist_vars[u, d] for d in self.dist_b_indices)

    def at_least_one_dist(self, u):
        assert u in self.v_f
        return at_least_one(self.dist_vars[u, d] for d in self.dist_b_indices)

    def verify_dist(self, u, d):
        assert u in self.v_f and d in self.dist_b_indices
        if d == 1:
            return self.dist_vars[u, d] == self.l_vars[self.v_star, u]
        return self.dist_vars[u, d] == at_least_one(
            self.l_vars[w, u] & self.dist_vars[w, d - 1]
            for w in self.afuddv if w != u
        )

    def reachable(self, u):
        assert u in self.dummy
        return at_least_one(self.dist_vars[u, d] for d in self.dist_b_indices)

    def not_leaf(self, u):
        assert u in self.dummy
        return ~self.reachable(u) | at_least_one(self.l_vars[u, w] for w in self.afuddv if w != u)

    def is_node(self, u):
        assert u in self.afud
        return aiger.atom(True) if u in self.a_f else self.reachable(u)

    def is_arc(self, u, v):
        assert u in self.afud and v in self.afud and u != v
        return self.is_node(u) & self.is_node(v) & self.l_vars[u, v] if v != self.v_star else aiger.atom(False)

    # for u, v in itertools.permutations(afud, 2):
    def beats(self, u, v):
        if u in self.a_f and v in self.a_f:
            if v in self.graph[u]:
                return aiger.atom(True)
            else:
                return aiger.atom(False)
        if u in self.a_f:
            return at_least_one(self.psi_vars[v, i] for i in self.naftypes if i > self.tau[u])
        if v in self.a_f:
            return at_least_one(self.psi_vars[u, i] for i in self.naftypes if i > self.tau[v])
        return at_least_one(self.psi_vars[u, i] & self.psi_vars[v, j]
                            for i, j in itertools.combinations(reversed(self.naftypes), 2))

    def if_arc_then_valid(self, u, v):
        assert u in self.afud and v in self.afud and u != v
        return self.is_arc(u, v).implies(self.beats(u, v))

    def in_closure(self, u):
        assert u in self.dummy
        return self.is_node(u) & at_least_one(self.l_vars[u, p] & self.l_vars[u, q]
                                              for p, q in itertools.combinations(self.afuddv, 2)
                                              if p != u and q != u)

    def child_of_closure(self, u):
        assert u in self.dummy
        return self.is_node(u) & ~self.in_closure(u)

    def no_deg2_consec_dum(self, u, v):
        assert u in self.dummy and v in self.dummy and u != v
        return (self.is_arc(u, v) & self.child_of_closure(u)).implies(self.child_of_closure(v))

    def loc_check_len_sensible(self, u, v):
        # for u, v in distinct2(afud) if v != v_star  # possibly should just be false/true for v_star
        assert u in self.afud and v in self.afud and u != v
        if v == self.v_star:
            # no arcs to v_star so implies short circuits
            return aiger.atom(True)
        return (self.is_arc(u, v) & (aiger.atom(True) if u in self.a_f else self.in_closure(u))
                ).implies(all_(~self.length_vars[u, v, b] for b in self.lln_indices))

    def loc_check_size_dec(self, u, v):
        assert u in self.afud and v in self.afud and u != v
        return self.is_arc(u, v).implies(
            at_least_one(all_(self.same_bit_vars[u, v, i] for i in self.ln_indices if i > b)  # largest condition
                         & self.chi_vars[u, b] & ~self.chi_vars[v, b]  # & ~self.same_bit_vars[u, v, b] ?
                         for b in self.ln_indices)
        )

    def loc_check_size_diff(self, u, v, w):
        assert u in self.afud and v in self.afud and w in self.afud
        return (self.is_arc(u, v) & self.is_arc(u, w)).implies(
            ~all_(self.same_bit_vars[v, w, b] for b in self.ln_indices)
        )

    def loc_check_path(self, u, v):
        assert u in self.afud and v in self.afud and u != v
        if v == self.v_star:
            # no arcs to v_star so implies short circuits
            return aiger.atom(True)
        if u not in self.dummy:
            return aiger.atom(False)
        same_bit_vars = [aiger.atom(f"same_{u}_{v}_{b}") for b in self.lln_indices]
        same_clauses = all_(same_bit_vars[b] == ((self.w_vars[u, b] & self.y_vars[u, v, b])
                                                 | (~self.w_vars[u, b] & ~self.y_vars[u, v, b]))
                            for b in self.lln_indices)
        return (self.is_arc(u, v) & self.child_of_closure(u)).implies(
            # all_(same_bit_vars) |  # equal
            at_least_one(all_(same_bit_vars[i] for i in self.lln_indices if i > b)  # largest condition
                         & self.w_vars[u, b] & ~self.y_vars[u, v, b]
                         for b in self.lln_indices)
        ) & same_clauses

    def realizable(self):
        return (
            self.variable_clauses
            # (i) Validity
            & all_(self.at_most_one_parent(u) for u in self.afuddv)
            & all_(self.exactly_one_type(u) for u in self.dummy)
            & all_(self.exactly_one_size_bit(u) for u in self.afud)
            & self.chi_vars[self.v_star, self.ln]
            & all_(self.at_most_one_dist(u) for u in self.afuddv)
            & all_(self.at_least_one_dist(u) for u in self.v_f)
            & all_(all_(self.verify_dist(u, d) for u in self.v_f) for d in self.dist_b_indices)
            & all_(self.reachable(u) for u in self.dummy)
            & all_(self.not_leaf(u) for u in self.dummy)
            # (ii)
            & all_(self.if_arc_then_valid(u, v)
                   & self.loc_check_len_sensible(u, v)
                   & self.loc_check_size_dec(u, v)
                   & self.loc_check_path(u, v)
                   for u, v in distinct2(self.afud))
            # (iii)
            & all_(self.loc_check_size_diff(u, v, w)
                   for u, v, w in itertools.permutations(self.afud, 3))
        )

    # def packing_node_sum(self, u):

    def packing_node_type(self, u, t):
        # what about u in a_f?
        assert u in self.dummy and t in self.naftypes
        return at_least_one(self.g_vars[u, t, b] for b in self.ln_indices).implies(
            at_least_one(self.psi_vars[u, i] for i in self.naftypes if i >= t))

    def packing_node_self(self, u):
        assert u in self.afud
        if u in self.a_f:
            # psi(u) isn't defined but it doesn't matter
            return aiger.atom(True)
        return all_(self.psi_vars[u, i].implies(
            at_least_one(self.g_vars[u, i, b] for b in self.ln_indices)
        ) for i in self.naftypes)

    def packable(self):
        return (
            # 1.
            all_(  # self.packing_node_sum(u)
                 all_(self.packing_node_type(u, t) for t in self.naftypes)
                 & all_(self.packing_node_self(u))
                 for u in self.afud)
        )

    def solve(self):
        r = self.realizable()
        print(r)
        return aiger_sat.solve(r)

def solve(graph):
    return {v for v in (1,) if solve_one(graph, v)}
