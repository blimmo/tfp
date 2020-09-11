import itertools


def twos(a):
    itr = iter(a)
    while True:
        try:
            yield next(itr), next(itr)
        except StopIteration:
            return


def draws(V):
    # TODO: filter identical draws
    return itertools.permutations(V)


def evaluate(tournament, draw):
    while len(draw) > 1:
        draw = [
            v if u in tournament[v] else u
            for u, v in twos(draw)
        ]
    return draw[0]


def solve(tournament):
    return {evaluate(tournament, s) for s in draws(tournament.v)}
