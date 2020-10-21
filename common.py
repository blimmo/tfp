import itertools

def all_vectors(template, s):
    return (v for v in itertools.product(*(range(p + 1) for p in template)) if sum(v) == s)

def twos(a):
    itr = iter(a)
    while True:
        try:
            yield next(itr), next(itr)
        except StopIteration:
            return
