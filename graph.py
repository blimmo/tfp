import itertools
import random
from collections import defaultdict
from copy import deepcopy

from common import twos


class Graph:
    def __init__(self, ln):
        self.ln = ln
        self.n = n = 2 ** ln
        self.v = v = frozenset(range(n))
        self.e = frozenset(itertools.combinations(v, 2))
        self.data = defaultdict(set)
        self.feedback = None
        self.order = None

    def __setitem__(self, key, value):
        self.data[key] = value

    def __getitem__(self, item):
        return self.data[item]

    def __str__(self):
        return str(self.data)

    def make_tournament(self, order=None, feedback=()):
        """Make the graph a tournament obeying a topological sort of order except feedback"""
        if order is None:
            order = tuple(range(self.n))
        self.order = order
        self.feedback = feedback

        self.data.clear()
        # add all edges according to order
        for u, v in self.e:
            for w in order:
                if w == u:
                    self.data[u].add(v)
                    break
                elif w == v:
                    self.data[v].add(u)
                    break
        # swap the feedback edges
        for u, v in feedback:
            if v in self.data[u]:
                self.data[v].add(u)
                self.data[u].remove(v)
            else:  # u in G[v]
                self.data[u].add(v)
                self.data[v].remove(u)

    def make_from_sba(self, winner):
        self.data.clear()
        remaining = set(self.v)
        remaining_e = {frozenset((u, v)) for u, v in self.e}
        while len(remaining) > 1:
            for u, v in twos(remaining.copy()):
                if u == winner:
                    first, second = u, v
                elif v == winner:
                    first, second = v, u
                else:
                    # arbitrary
                    if random.choice((True, False)):
                        first, second = u, v
                    else:
                        first, second = v, u
                self.data[first].add(second)
                remaining.remove(second)
                remaining_e.remove(frozenset((u, v)))
        for u, v in remaining_e:
            if random.choice((True, False)):
                self.data[u].add(v)
            else:
                self.data[v].add(u)

    def find_feedback(self):
        # if self.feedback is not None:
        #     return self.feedback
        f = self.feedback_rec(self.data)
        self.feedback = f
        return f

    def feedback_rec(self, d):
        possible = itertools.chain.from_iterable(
            ((u, v), (v, w), (w, u))
            for u, v, w in itertools.permutations(d.keys(), 3)
            if v in d[u] and w in d[v] and u in d[w]
        )
        best = ()
        for x, y in possible:
            # swap (x, y)
            d_new = deepcopy(d)
            d_new[x].remove(y)
            d_new[y].add(x)
            ret = self.feedback_rec(d_new)
            if len(ret) > len(best):
                best = ret + ((x, y),)
        return best
