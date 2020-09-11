import itertools
from collections import defaultdict


class Graph:
    def __init__(self, ln):
        self.ln = ln
        self.n = n = 2 ** ln
        self.v = v = frozenset(range(n))
        self.e = frozenset(itertools.combinations(v, 2))
        self.data = defaultdict(set)

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
