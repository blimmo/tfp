import itertools

from common import twos

def halves(players):
    for i in itertools.combinations(players[1:], len(players) // 2 - 1):
        first = i + (players[0],)
        yield first, tuple(j for j in players if j not in first)

def draws(players):
    if len(players) <= 2:
        yield players
        return
    for half, other in halves(players):
        for half_draw in draws(half):
            for other_draw in draws(other):
                yield half_draw + other_draw


def evaluate(tournament, draw):
    while len(draw) > 1:
        draw = [
            v if u in tournament[v] else u
            for u, v in twos(draw)
        ]
    return draw[0]


def solve(tournament):
    def f(players):
        if len(players) == 1:
            return players
        return {v if u in tournament[v] else u
                for half, other in halves(players)
                for u in f(half) for v in f(other)}
    return f(tuple(tournament.v))

def solve_old(tournament):
    return {evaluate(tournament, s) for s in draws(list(tournament.v))}


if __name__ == "__main__":
    print(list(halves(tuple(range(8)))))
    print(list(draws(tuple(range(8)))))
