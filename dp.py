from collections import defaultdict

from common import all_vectors


def solve(G):
    return {v for v in G.v if solve_one(G, v)}


def solve_one(G, v_star):
    tau = {}
    """Map from vertices to colours"""
    mu = [0]
    """Map from colours to number of vertices with that colour"""
    adjacent = defaultdict(set)
    """Map from c to colours c beats"""

    v_f = frozenset(sum(G.feedback, start=()))
    a_f = v_f.union((v_star,))
    # find colours
    for v in G.order:
        if v in a_f:
            mu.append(0)
            mu[-1] += 1
            tau[v] = len(mu) - 1
            mu.append(0)
        else:
            mu[-1] += 1
            tau[v] = len(mu) - 1
    mu = tuple(mu)
    c = len(mu)
    for u in G.v:
        adjacent[tau[u]].update({tau[v] for v in G[u]})

    result = [
        [
            set()
            for _ in range(c)]
        for _ in range(G.ln + 1)]
    """Map from height and colour that wins to set of vectors of amount of each colour used that work"""

    # base cases
    result[0] = [{b for b in all_vectors(mu, 1) if b[i] == 1} for i in range(c)]

    # DP
    for x in range(1, G.ln + 1):
        for winning_colour in range(c):
            for possible in all_vectors(mu, 2 ** x):
                # calculate whether to add possible to result[x, winning_colour]
                for winning_sub in all_vectors(possible, 2 ** (x - 1)):
                    if winning_sub in result[x - 1][winning_colour]:
                        for other_colour in range(c):
                            if (winning_sub[other_colour] != possible[other_colour] and
                                    other_colour in adjacent[winning_colour]):
                                # other_colours left to win the other tournament
                                # and winning_colour beats other_colour
                                other_sub = tuple(possible[i] - winning_sub[i] for i in range(c))
                                if other_sub in result[x - 1][other_colour]:
                                    result[x][winning_colour].add(possible)
    return mu in result[G.ln][tau[v_star]]

if __name__ == "__main__":
    # 5; 10; ((5, 13), (14, 1), (12, 26), (14, 28), (17, 0))
    # mu = (0, 1, 0, 1, 3, 1, 4, 1, 1, 1, 0, 1, 0, 1, 2, 1, 8, 1, 1, 1, 3)
    # 5; 5; [(0, 2), (3, 7), (2, 5), (0, 6), (1, 8)]
    # mu = (0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 23)
    # 6; 3; ((0, 57), (34, 29), (13, 40))
    # mu = (0, 1, 2, 1, 9, 1, 15, 1, 4, 1, 5, 1, 16, 1, 6)
    # 5; 27; ((0, 14), (3, 19), (6, 11))
    mu = (0, 1, 2, 1, 2, 1, 4, 1, 2, 1, 4, 1, 7, 1, 4)
    for x in range(1, 7):
        print(len(list(all_vectors(mu, 2 ** x))))
