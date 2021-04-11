import itertools
from collections import defaultdict


def all_vectors(template, s):  # roughly N_x
    return (v for v in itertools.product(*(range(p + 1) for p in template)) if sum(v) == s)

def twos(a):
    itr = iter(a)
    while True:
        try:
            yield next(itr), next(itr)
        except StopIteration:
            return

def calculate_tau(graph, a_f):
    tau = {}
    invtau = defaultdict(set)
    cur = 0
    for v in graph.order:
        if v in a_f:
            tau[v] = cur + 0.5
            invtau[cur + 0.5].add(v)
            cur += 1
        else:
            tau[v] = cur
            invtau[cur].add(v)
    return tau, invtau
