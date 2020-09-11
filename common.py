import itertools

def all_vectors(template, s):
    return (v for v in itertools.product(*(range(p + 1) for p in template)) if sum(v) == s)
