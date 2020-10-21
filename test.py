import itertools
import os

import bruteforce
import dp
import ilp
from graph import Graph


def powerset(s):
    "powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)"
    return itertools.chain.from_iterable(itertools.combinations(s, r) for r in range(len(s)+1))


tournament = Graph(3)
# for order in itertools.permutations(V):
if os.getenv("DEBUG") is None:
    to_iter = enumerate(powerset(tournament.e))
else:
    DEBUG = int(os.getenv("DEBUG"))
    to_iter = enumerate(itertools.islice(powerset(tournament.e), DEBUG, DEBUG + 1))
for i, feedback in to_iter:
    tournament.make_tournament(feedback=feedback)
    print(i, feedback, tournament)

    # first solve by brute force
    winners = bruteforce.solve(tournament)

    # n^k algo
    # result = dp.solve(tournament)
    # if not fpt.check_positive(tournament, winners):
    #     print()
    #     print("!----------------------!")
    #     print()
    #
    result = ilp.solve(tournament)
    if result != winners:
        print()
        print("!----------------------!")
        print(winners, result)
        print("!----------------------!")
        print()
