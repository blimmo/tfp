import itertools
import networkx
import pulp
from pulp import lpSum as csum
# import mip

from common import all_vectors

solver = pulp.PULP_CBC_CMD(msg=False)

def check_positive(G, winners):
    for v in winners:
        if not solve_one(G, v):
            return False
    return True

def solve(G):
    return {v for v in G.v if solve_one(G, v)}


def possible_chi(ln, i):
    if i > 2 ** ln:
        raise ValueError("Can't make that many")
    possible = tuple(2 ** x for x in range(ln - 1, -1, -1))
    return rec(possible, (ln,), i - 1, None)

def rec(possible, out, remaining, last):
    if remaining == 0:
        yield out
    else:
        for j, a in enumerate(possible):
            if a == 0 or j == last:
                continue
            for k in range(1, min(a, remaining) + 1):
                yield from rec(possible[:j] + (a - k,) + possible[j + 1:], out + (j,) * k, remaining - k, j)



def solve_one(G, v_star):
    count = 0
    # print(v_star)
    if G.feedback == ():
        return v_star == G.order[0]

    a_f_set = set(sum(G.feedback, start=(v_star,)))
    a_f = tuple(x for x in G.order if x in a_f_set)
    v_star_ind = a_f.index(v_star)
    a_f_to_add = [i + 0.5 for i in range(len(a_f)) if i != v_star_ind]
    # calculate tau
    tau = {}
    num = [0]
    for v in G.order:
        if v in a_f:
            tau[v] = len(num) - 0.5
            num.append(0)
        else:
            tau[v] = len(num) - 1
            num[-1] += 1
    num = tuple(num)

    max_h = min(8 * len(a_f), G.n)
    for total_vertices in range(len(a_f), max_h + 1):
        # how much bigger is b_f than a_f
        extra_vertices = total_vertices - len(a_f)
        # guess a tree for H
        for p_seq in itertools.product(range(total_vertices), repeat=total_vertices - 2):
            undir_h = networkx.from_prufer_sequence(p_seq)
            # guess a root of H
            # for root in range(total_vertices):
            root = 0
            # tree -> arborescence
            h = networkx.DiGraph()
            for u, v in networkx.dfs_edges(undir_h, root):
                h.add_edge(u, v)
            # guess the types of the extra vertices
            for psi_vec in all_vectors(num, extra_vertices):
                psi_vec = list(psi_vec)
                others_to_add = []
                while True:
                    for j, v in enumerate(psi_vec):
                        if v > 0:
                            others_to_add.append(j)
                            psi_vec[j] -= 1
                            break
                    else:
                        break
                unsorted_psi = a_f_to_add + others_to_add
                for psi in itertools.permutations(unsorted_psi):
                    # add v_star as root
                    psi = (v_star_ind + 0.5,) + psi
                    # check h obeys G
                    for u, v in h.edges:
                        if isinstance(psi[u], int) or isinstance(psi[v], int):
                            if psi[u] > psi[v]:
                                break
                        elif a_f[int(psi[v])] not in G[a_f[int(psi[u])]]:
                            break
                    else:
                        # guess the number of vertices below each vertex of H
                        # for chi in itertools.product(range(G.ln + 1), repeat=total_vertices):
                        for chi in possible_chi(G.ln, total_vertices):
                            count += 1
                            if solve_ilp(num, a_f, h, tau, chi, psi):
                                return True
            # print(count)
        # print(count, total_vertices)
    # print("!", v_star, count)
    # print(count)
    return False


def solve_ilp(num, a_f, h, tau, chi, psi):
    # prob = mip.Model()
    # prob.emphasis = mip.SearchEmphasis.FEASIBILITY
    # prob.verbose = 0
    prob = pulp.LpProblem("p")
    types = tuple(i / 2 for i in range(2 * len(a_f) + 1))
    vertices = tuple(h.nodes)
    variables = pulp.LpVariable.dicts("x", (types, vertices), lowBound=0, cat=pulp.const.LpInteger)
    # variables = {i: [prob.add_var(name=f"x_{i}_{v}", var_type=mip.INTEGER, lb=0) for v in vertices] for i in types}
    # C_1
    for i in types:
        prob += csum([variables[i][u] for u in vertices]) == (num[int(i)] if i.is_integer() else 1), f"C_1_{i}"
    for u in vertices:
        # C_2. Should be only for vertices not in a_f?
        colour = psi[u]
        prob += variables[colour][u] >= 1, f"C_2_{u}"
        # C_3
        lhs = []
        for i in types:
            if i >= colour:
                lhs.append(variables[i][u])
            else:
                # C_4
                prob += variables[i][u] == 0, f"C_4_{i}_{u}"
        rhs = 2 ** chi[u] - sum(2 ** chi[v] for v in h.successors(u))
        prob += csum(lhs) == rhs, f"C_3_{u}"

    # status = prob.optimize(max_solutions=1)
    prob.solve(solver)
    status = prob.status
    # print(".", end="")
    # if status in (mip.OptimizationStatus.INFEASIBLE, mip.OptimizationStatus.NO_SOLUTION_FOUND):
    if status == pulp.LpStatusInfeasible:
        return False
    # elif status in (mip.OptimizationStatus.FEASIBLE, mip.OptimizationStatus.OPTIMAL):
    elif status == pulp.LpStatusOptimal:
        # print(tau)
        # print("     " + " ".join(str(v) for v in vertices) + f"   ({a_f}, {psi})")
        # for i in types:
        #     print(f"{i}: ", end="")
        #     for v in vertices:
        #         print(int(variables[i][v].varValue), end=" ")
        #     print()
        # solve_ilp(num, a_f, h, tau, chi, psi)
        return True
    else:
        raise ValueError(f"Unknown status {status}")
