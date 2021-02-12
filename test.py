import itertools
import os

import bruteforce
import dp
import ilp
import sat
from graph import Graph


def powerset(s):
    "powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)"
    return itertools.chain.from_iterable(itertools.combinations(s, r) for r in range(len(s)+1))


tournament = Graph(2)
# for order in itertools.permutations(V):
if os.getenv("DEBUG") is None:
    to_iter = enumerate(itertools.islice(powerset(tournament.e), 0, None))
else:
    DEBUG = int(os.getenv("DEBUG"))
    to_iter = enumerate(itertools.islice(powerset(tournament.e), DEBUG, DEBUG + 1))
for i, feedback in to_iter:
    tournament.make_tournament(feedback=feedback)
    if any(v.union([k]) == tournament.v for k, v in tournament.data.items()):
        # skip trivial cases
        print(i, end=" ")
        continue
    print("\n", i, feedback, tournament)
    winners = bruteforce.solve(tournament)
    print(winners, end=" ")
    result = set()
    for v_star in tournament.v:
        print(v_star, end="")
        dpr = dp.solve_one(tournament, v_star)
        satr = sat.solve_one(tournament, v_star)
        if dpr != satr:
            print(dpr, satr)
            raise Exception()
        if satr:
            result.add(v_star)
        # print(result)

    # first solve by brute force

    # n^k algo
    # print(dp.solve(tournament))
    # if not fpt.check_positive(tournament, winners):
    #     print()
    #     print("!----------------------!")
    #     print()
    #
    # result = ilp.solve(tournament)
    if result != winners:
        print()
        print("!----------------------!")
        print(winners, result)
        print("!----------------------!")
        print()
        break
