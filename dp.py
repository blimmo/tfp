import os
from collections import defaultdict

from common import all_vectors


def solve(G):
    return {v for v in G.v if solve_one(G, v)}


def solve_one(G, v_star):
    colour = {}
    """Map from vertices to colours"""
    num = [0]
    """Map from colours to number of vertices with that colour"""
    adjacent = defaultdict(set)
    """Map from c to colours c beats"""

    # find colours
    change = False
    for v in G.order:
        if v == v_star:
            # v_star should always have its own colour
            num.append(0)
            change = True
        else:
            if change:
                num.append(0)
                change = False
            for u, w in G.feedback:
                if u == v or w == v:
                    num.append(0)
                    change = True
                    break
        num[-1] += 1
        colour[v] = len(num) - 1
    num = tuple(num)
    c = len(num)
    for u in G.v:
        adjacent[colour[u]].update({colour[v] for v in G[u]})

    result = [
        [
            set()
            for _ in range(c)]
        for _ in range(G.ln + 1)]
    """Map from height and colour that wins to set of vectors of amount of each colour used that work"""

    # base cases
    result[0] = [{b for b in all_vectors(num, 1) if b[i] == 1} for i in range(c)]

    # DP
    for x in range(1, G.ln + 1):
        for winning_colour in range(c):
            for possible in all_vectors(num, 2 ** x):
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
    if os.getenv("DEBUG") is not None:
        print(colour)
        print(num)
        # print(result)
    return num in result[G.ln][colour[v_star]]
