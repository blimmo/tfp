import itertools
import math
import operator
from collections import defaultdict
from functools import partial, reduce
from pprint import pprint

import networkx as nx
import sympy

import glucose_wrapper

# shims
new_var = partial(sympy.Symbol)
implies = sympy.Implies
equivalent = sympy.Equivalent
true = sympy.true
false = sympy.false
solve_expr = glucose_wrapper.glucose_satisfiable  # sympy.logic.inference.satisfiable

def flatten(a):
    return reduce(operator.iconcat, a, [])

def pretty(result):
    pprint([item for item in result
            if ("L_" in item[0])
            or ("psi_" in item[0])
            # or ("chi_" in item[0])
            # or ("len_" in item[0])
            or ("g_" in item[0])])

def at_most_one(literals):
    return sympy.logic.And(*(~a | ~b for a, b in itertools.combinations(literals, 2)))

def at_least_one(literals):
    return sympy.logic.Or(*literals)

def exactly_one(literals):
    literals = list(literals)
    return at_most_one(literals) & at_least_one(literals)

def all_(literals):
    return sympy.logic.And(*literals)

def distinct2(s):
    return tuple(itertools.permutations(s, 2))

def bin_arb(nodes):
    assert len(nodes) > 0
    if len(nodes) == 1:
        arb = nx.DiGraph()
        arb.add_nodes_from(nodes)
        return arb, nodes[0]
    arb1, root1 = bin_arb(nodes[:len(nodes) // 2])
    arb2, root2 = bin_arb(nodes[len(nodes) // 2:])
    arb = nx.union(arb1, arb2)
    arb.add_edge(root1, root2)
    return arb, root1

def solve_one(graph, v_star, decision=True):
    # print(f"v_star = {v_star}")
    v_f = frozenset(sum(graph.feedback, start=()))
    a_f = v_f.union((v_star,))
    for k, v in graph.data.items():
        if v.union([k]) == graph.v:
            return k == v_star

    tau = {}
    invtau = defaultdict(set)
    cur = 0
    for v in graph.order:
        if v in a_f:
            tau[v] = cur + 0.5
            invtau[cur + 0.5].add(v)
            cur += 1
        else:
            tau[v] = cur
            invtau[cur].add(v)
    naftypes = tuple(range(cur + 1))
    num = tuple(len(invtau[t]) for t in naftypes)
    # types = tuple(i / 2 for i in range(2 * len(a_f) + 1))

    max_dummy_size = min(4 * len(a_f), graph.n) - len(a_f)  # maybe 4 * len(a_f)?
    for dummy_size in range(max_dummy_size + 1):
        dummy = {-i for i in range(1, dummy_size + 1)}
        cond = Conditions.make(graph, v_star, v_f, a_f, dummy, naftypes, tau, invtau, num)
        result = cond.solve()
        print(".", end="")
        if result is not False:
            if decision:
                return True
            else:
                return cond.decode(result)  # [(cond.inverse_lookup(k), v) for k, v in result.items()]
    if decision:
        return False
    else:
        return None

class Conditions:
    def __init__(self, graph=None, ln=None, v_star=None, v_f=None, a_f=None, dummy=None,
                 naftypes=None, tau=None, invtau=None, num=None, afud=None, afuddv=None):
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
        self.invtau = invtau
        self.num = num
        self.afud = afud
        self.afuddv = afuddv
        if afud is not None:
            self.afud_and_pairs = afud.union(distinct2(afud))
        self.variable_clauses = []

    @classmethod
    def make(cls, graph, v_star, v_f, a_f, dummy, typesaf, tau, invtau, num):
        afud = a_f.union(dummy)
        ins = cls(graph, graph.ln, v_star, v_f, a_f, dummy, typesaf, tau, invtau, num,
                  afud, afud.difference({v_star}))
        ins.gen_l_vars()
        ins.gen_psi_vars()
        ins.gen_chi_vars()
        ins.gen_length_vars()
        ins.gen_dist_vars()
        ins.gen_same_bit_vars()
        ins.gen_g_vars()
        return ins

    def decode(self, rresult):
        result = {str(k) for k, v in rresult.items() if v}
        arb = nx.DiGraph()
        overflow = set()
        dummy_map = {}
        for k, v in self.l_vars.items():
            if str(v) in result:
                print("L", k)
                arb.add_edge(*k)
        for (u, i), v in self.psi_vars.items():
            if str(v) in result:
                print("psi", u, i)
                dummy_map[u] = self.invtau[i].pop()
                overflow.add((u, i))
        for (e, i), lv in self.g_vars.items():
            for b, v in enumerate(lv):
                if str(v) in result:
                    print("g", e, i, 2 ** b)
                    try:
                        u, v = e
                    except TypeError:
                        # e is a node
                        count = 2 ** b
                        if e in self.dummy and (e, i) in overflow:
                            # g(u, psi(u)) is 1 too big
                            overflow.remove((e, i))
                            count -= 1
                            if count == 0:
                                continue
                        children = sorted([self.invtau[i].pop() for _ in range(count)])
                        subarb, root = bin_arb(children)
                        arb = nx.union(arb, subarb)
                        arb.add_edge(e, root)
                    else:
                        # e is an edge
                        print(u, v, i, 2 ** b)
                    # g[e, i] += 2 ** b
        nx.relabel_nodes(arb, dummy_map, copy=False)
        return arb

    def gen_l_vars(self):
        self.l_vars = ret = {
            (u, v): new_var(f"L_{u}->{v}")
            for u, v in distinct2(self.afud)
            if v != self.v_star
        }
        return ret

    def gen_psi_vars(self):
        self.psi_vars = ret = {
            (u, i): new_var(f"psi_{u}<={i}")
            for u in self.dummy
            for i in self.naftypes
        }
        return ret

    def gen_chi_vars(self):
        self.chi_vars = ret = {
            u: [new_var(f"chi_u:{u}_b:{b}") for b in self.ln_indices]
            for u in self.afud
        }
        return ret

    def gen_length_vars(self):
        self.length_vars = ret = {
            (u, v): [new_var(f"len_{u}->{v}_{b}") for b in self.lln_indices]
            for u, v in distinct2(self.afud)
            if v != self.v_star
        }
        return ret

    def gen_dist_vars(self):
        self.dist_b_indices = list(range(1, self.ln + 1))
        self.dist_vars = ret = {
            (u, d): new_var(f"dist_{u}_{d}")
            for u in self.afuddv
            for d in self.dist_b_indices
        }
        return ret

    def gen_g_vars(self):
        self.g_vars = {
            (e, i): [new_var(f"g_{e}_{i}_{b}") for b in self.ln_indices]
            for e in self.afud_and_pairs
            for i in self.naftypes
        }

    def gen_same_bit_vars(self):
        """For LocCheckSize(Dec/Diff)"""
        # TODO: Generalise same
        self.same_bit_vars = same_bit_vars = {(u, v): [new_var(f"samebit_{u}_{v}_{b}") for b in self.ln_indices]
                                              for u, v in distinct2(self.afud)}
        self.variable_clauses.append(all_(all_(equivalent(same_bit_vars[u, v][b], ((self.chi_vars[u][b] & self.chi_vars[v][b])
                                                                      | (~self.chi_vars[u][b] & ~self.chi_vars[v][b])))
                                           for b in self.ln_indices)
                                      for u, v in distinct2(self.afud)))
        return same_bit_vars

    def sum(self, x, y, prefix):
        # assert len(x) == len(y)
        if len(x) < len(y):
            x = x + [false] * (len(y) - len(x))
        elif len(y) < len(x):
            y = y + [false] * (len(x) - len(y))
        indices = list(range(len(x)))
        result_vars = [new_var(f"{prefix}_b:{b}") for b in indices]
        c = [new_var(f"{prefix}_carry:{b}") for b in indices]
        clauses = [equivalent(c[0], x[0] & y[0])]  # first carry doesn't consider previous ones
        clauses += [equivalent(c[b], sympy.logic.Or(x[b] & y[b], x[b] & c[b - 1], y[b] & c[b - 1]))
                    for b in indices[1:]]
        clauses.append(equivalent(result_vars[0], x[0] ^ y[0]))
        clauses += [equivalent(result_vars[b], sympy.logic.Xor(x[b], y[b], c[b - 1]))
                    for b in indices[1:]]
        clauses.append(equivalent(c[-1], false))
        self.variable_clauses += clauses
        return result_vars

    # validity
    def at_most_one_parent(self, u):
        assert u in self.afuddv
        return at_most_one(self.l_vars[v, u] for v in self.afud if v != u)

    def exactly_one_type(self, u):
        assert u in self.dummy
        return exactly_one(self.psi_vars[u, i] for i in self.naftypes)

    def exactly_one_size_bit(self, u):
        assert u in self.afud
        return exactly_one(self.chi_vars[u][b] for b in self.ln_indices)

    def at_most_one_dist(self, u):
        assert u in self.afuddv
        return at_most_one(self.dist_vars[u, d] for d in self.dist_b_indices)

    def at_least_one_dist(self, u):
        assert u in self.afuddv
        return at_least_one(self.dist_vars[u, d] for d in self.dist_b_indices)

    def verify_dist(self, u, d):
        assert u in self.afuddv and d in self.dist_b_indices
        if d == 1:
            return equivalent(self.dist_vars[u, d], self.l_vars[self.v_star, u])
        return equivalent(self.dist_vars[u, d], at_least_one(
            self.l_vars[w, u] & self.dist_vars[w, d - 1]
            for w in self.afuddv if w != u
        ))

    def reachable(self, u):
        assert u in self.dummy
        return at_least_one(self.dist_vars[u, d] for d in self.dist_b_indices)

    def not_leaf(self, u):
        assert u in self.dummy
        return ~self.reachable(u) | at_least_one(self.l_vars[u, w] for w in self.afuddv if w != u)

    def is_node(self, u):
        assert u in self.afud
        return true if u in self.a_f else self.reachable(u)

    def is_arc(self, u, v):
        assert u in self.afud and v in self.afud and u != v
        return self.is_node(u) & self.is_node(v) & self.l_vars[u, v] if v != self.v_star else false

    # for u, v in itertools.permutations(afud, 2):
    def beats(self, u, v):
        if u in self.a_f and v in self.a_f:
            if v in self.graph[u]:
                return true
            else:
                return false
        if u in self.a_f:
            return at_least_one(self.psi_vars[v, i] for i in self.naftypes if i > self.tau[u])
        if v in self.a_f:
            return at_least_one(self.psi_vars[u, i] for i in self.naftypes if i < self.tau[v])  # maybe >?
        return at_least_one(self.psi_vars[u, i] & self.psi_vars[v, j]
                            for i, j in itertools.combinations(self.naftypes, 2))  # maybe reversed?

    def if_arc_then_valid(self, u, v):
        assert u in self.afud and v in self.afud and u != v
        return implies(self.is_arc(u, v), self.beats(u, v))

    def in_closure(self, u):
        if u in self.dummy:
            return self.is_node(u) & at_least_one(self.l_vars[u, p] & self.l_vars[u, q]
                                                  for p, q in itertools.combinations(self.afuddv, 2)
                                                  if p != u and q != u)
        else:
            return false

    def child_of_closure(self, u):
        if u in self.dummy:
            return self.is_node(u) & ~self.in_closure(u)
        else:
            return false

    def no_deg2_consec_dum(self, u, v):
        assert u in self.dummy and v in self.dummy and u != v
        return implies(self.is_arc(u, v) & self.child_of_closure(u), self.child_of_closure(v))

    def loc_check_len_sensible(self, u, v):
        # for u, v in distinct2(afud) if v != v_star  # possibly should just be false/true for v_star
        assert u in self.afud and v in self.afud and u != v
        if v == self.v_star:
            # no arcs to v_star so implies short circuits
            return true
        return implies(self.is_arc(u, v) & (true if u in self.a_f else self.in_closure(u)),
                       all_(~self.length_vars[u, v][b] for b in self.lln_indices))

    def loc_check_size_dec(self, u, v):
        assert u in self.afud and v in self.afud and u != v
        return implies(
            self.is_arc(u, v),
            at_least_one(all_(self.same_bit_vars[u, v][i] for i in self.ln_indices if i > b)  # largest condition
                         & self.chi_vars[u][b] & ~self.chi_vars[v][b]  # & ~self.same_bit_vars[u, v, b] ?
                         for b in self.ln_indices)
        )

    def loc_check_size_diff(self, u, v, w):
        assert u in self.afud and v in self.afud and w in self.afud
        return implies(
            self.is_arc(u, v) & self.is_arc(u, w),
            ~all_(self.same_bit_vars[v, w][b] for b in self.ln_indices)
        )

    def loc_check_path(self, u, v):
        assert u in self.afud and v in self.afud and u != v
        if v == self.v_star:
            # no arcs to v_star so implies short circuits
            return true
        w_vars = {v: [new_var(f"w_{v}_{b}") for b in self.lln_indices]
                  for v in self.afud}
        self.variable_clauses += flatten([[implies(self.chi_vars[v][b], (all_(
            w_vars[v][i] if ((b >> i) & 1) == 1 else ~w_vars[v][i]
            for i in self.lln_indices))) for b in self.ln_indices] for v in self.afud])  # maybe equivalent?
        y_vars = {
            (u, v): self.sum(w_vars[v], self.length_vars[u, v], f"chi+l_u:{u}_v:{v}")
            for u, v in distinct2(self.afud)
            if v != self.v_star
        }
        # if u not in self.dummy:
        #     return aiger.atom(False)
        same_bit_vars = [new_var(f"same_{u}_{v}_{b}") for b in self.lln_indices]
        self.variable_clauses += [equivalent(same_bit_vars[b], ((w_vars[u][b] & y_vars[u, v][b])
                                                                | (~w_vars[u][b] & ~y_vars[u, v][b])))
                                  for b in self.lln_indices]
        return implies(
            self.is_arc(u, v) & self.child_of_closure(u),
            # all_(same_bit_vars) |  # equal
            at_least_one(all_(same_bit_vars[i] for i in self.lln_indices if i > b)  # largest condition
                         & w_vars[u][b] & ~y_vars[u, v][b]
                         for b in self.lln_indices)
        )

    def realizable(self):
        return flatten((
            # (i) Validity
            [self.at_most_one_parent(u) for u in self.afuddv],
            [self.exactly_one_type(u) for u in self.dummy],
            [self.exactly_one_size_bit(u) for u in self.afud],
            [self.chi_vars[self.v_star][self.ln]],
            [self.at_most_one_dist(u) for u in self.afuddv],
            [self.at_least_one_dist(u) for u in self.afuddv],
            [all_(self.verify_dist(u, d) for u in self.afuddv) for d in self.dist_b_indices],
            [self.reachable(u) for u in self.dummy],
            [self.not_leaf(u) for u in self.dummy],
            # (ii)
            [self.if_arc_then_valid(u, v) for u, v in distinct2(self.afud)],
            [self.loc_check_len_sensible(u, v) for u, v in distinct2(self.afud)],
            [self.loc_check_size_dec(u, v) for u, v in distinct2(self.afud)],
            [self.loc_check_path(u, v) for u, v in distinct2(self.afud)],
            # (iii)
            [self.loc_check_size_diff(u, v, w) for u, v, w in itertools.permutations(self.afud, 3)]
        ))

    def packing_node_sum(self, u):
        assert u in self.afud
        lhs = [true if u in self.a_f else false]  # u itself is counted in chi
        for t in self.naftypes:
            lhs = self.sum(lhs, self.g_vars[u, t], f"pnslhs:{u}_{t}")
        for v in self.afuddv:
            if v == u:
                continue
            belowv = self.sum(self.chi_vars[v], self.length_vars[u, v], f"chi({v})+l({u})")
            lhs = self.sum(
                lhs,
                [self.l_vars[u, v] & var for var in belowv],
                f"pnslhs2:{u}_{v}"
            )
        return all_(equivalent(lv, rv) for lv, rv in zip(lhs, self.chi_vars[u]))

    def types_beats(self, u, threshold, u_wins):
        # strict inequalities?
        comp = operator.le if u_wins else operator.ge
        if u in self.dummy:
            return at_least_one(self.psi_vars[u, i] for i in self.naftypes if comp(i, threshold))
        else:  # u in self.a_f
            return true if comp(self.tau[u], threshold) else false
        #  and self.num[threshold] > 0 ?

    def packing_node_type(self, u, t):
        assert u in self.afud and t in self.naftypes
        return implies(at_least_one(self.g_vars[u, t][b] for b in self.ln_indices), self.types_beats(u, t, True))

    def packing_node_self(self, u):
        assert u in self.afud
        if u in self.a_f:
            # psi(u) isn't defined but it doesn't matter
            return true
        return all_(implies(self.psi_vars[u, i],
                            at_least_one(self.g_vars[u, i][b] for b in self.ln_indices)
        ) for i in self.naftypes)

    def packing_arc_sum(self, a):
        u, v = a
        i = iter(self.naftypes)
        lhs = self.g_vars[a, next(i)]
        for j, t in enumerate(i):
            lhs = self.sum(lhs, self.g_vars[a, t], f"pas:{a}_{t}")
        return all_(
            equivalent(lv, rv) for lv, rv in zip(lhs, self.length_vars[u, v])
        )

    def packing_arc_type(self, a, t):
        u, v = a
        return implies(
            at_least_one(self.g_vars[a, t]),
            self.types_beats(u, t, True) & self.types_beats(v, t, False)
        )

    def packing_type_sum(self, t):
        i = iter(self.afud_and_pairs)
        lhs = self.g_vars[next(i), t]
        for j, e in enumerate(i):
            lhs = self.sum(lhs, self.g_vars[e, t], f"pts:{e}_{t}")
        return all_(
            v if ((self.num[t] >> b) & 1) == 1 else ~v for b, v in enumerate(lhs)
        )

    def packable(self):
        return flatten((
            # 1.
            [self.packing_node_sum(u) for u in self.afud],
            flatten([self.packing_node_type(u, t) for t in self.naftypes] for u in self.afud),
            [self.packing_node_self(u) for u in self.afud],
            # 2.
            [self.packing_arc_sum(a) for a in distinct2(self.afud) if a[1] != self.v_star],
            flatten([self.packing_arc_type(a, t) for t in self.naftypes]
                    for a in distinct2(self.afud) if a[1] != self.v_star),
            # 3.
            [self.packing_type_sum(t) for t in self.naftypes]
        ))

    def solve(self):
        r = self.realizable()
        p = self.packable()
        return solve_expr(self.variable_clauses + r + p)

def solve(graph):
    return {v for v in graph.v if solve_one(graph, v)}
