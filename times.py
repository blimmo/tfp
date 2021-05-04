import random
import time

import dp
import sat
from graph import Graph

random.seed(0)

repeats = 5
for k in range(2, 8):
    ln = k
    tournament = Graph(ln)
    i = 0
    j = 0
    while i < repeats or j < repeats:
        feedback = tuple(tuple(random.sample(tuple(tournament.v), k=2)) for _ in range(k))
        v_star = random.choice(tuple(tournament.v))
        tournament.make_tournament(feedback=feedback)
        if any(v.union([k]) == tournament.v for k, v in tournament.data.items()):
            # skip trivial cases
            continue

        print(ln, v_star, feedback, end="; ", sep="; ")
        start = time.perf_counter()
        result = sat.solve_one(tournament, v_star)
        satt = time.perf_counter() - start
        print(result, satt, end="; ")

        start = time.perf_counter()
        dpr = dp.solve_one(tournament, v_star)
        dpt = time.perf_counter() - start
        print(dpr, dpt, end="; ")

        start = time.perf_counter()
        oldr = sat.solve_one(tournament, v_star, improvement=False)
        oldt = time.perf_counter() - start
        print(oldr, oldt, end="\n")

        if result != dpr or dpr != oldr:
            print("!!!")
            break
        file = "out/true.txt" if result else "out/false.txt"
        with open(file, "a") as f:
            print(ln, v_star, feedback, satt, dpt, oldt, sep="; ", file=f)
        if result:
            i += 1
        else:
            j += 1
