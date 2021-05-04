import itertools
import random

import bruteforce
import dp
# import ilp
import sat
from graph import Graph
import demo


def powerset(s):
    "powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)"
    return itertools.chain.from_iterable(itertools.combinations(s, r) for r in range(len(s)+1))

ln = 4
tournament = Graph(ln)
for i, feedback in enumerate(itertools.islice(powerset(tournament.e), 200, None)):
    feedback = tuple(tuple(random.sample(tuple(tournament.v), k=2)) for _ in range(3))
    tournament.make_tournament(feedback=feedback)
    if any(v.union([k]) == tournament.v for k, v in tournament.data.items()):
        # skip trivial cases
        print(i, end=" ")
        continue
    print("\n", i, feedback, tournament)
    if ln < 4:
        winners = bruteforce.solve(tournament)
    else:
        winners = dp.solve(tournament)
    print(winners, end=" ")
    result = set()
    # for v_star in tournament.v:
    for v_star in winners:
        print(v_star, end="")
        satr = sat.solve_one(tournament, v_star, decision=False)
        if satr is not None:
            result.add(v_star)
            if satr[1]:
                demo.show(satr[0], v_star)
    print(result)

    if result != winners:
        print()
        print("!----------------------!")
        print(winners, result)
        print("!----------------------!")
        print()
        break
