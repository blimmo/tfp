import time

from graph import Graph
import sat
import bruteforce
import dp

# 8 runs out of memory
ln = 5
feedback = [(0, 5), (2, 7), (6, 7), (6, 5), (8, 9)]
[
    (0, 3),
    (1, 3),
    (0, 5),
    (2, 7),
    (6, 7),
    # (6, 5),
    # (8, 9),
    # (12, 15),
    # (10, 15),
]
v_star = 3
tournament = Graph(ln)
tournament.make_tournament(feedback=feedback)
print(ln, v_star, feedback)

if ln < 4:
    start = time.perf_counter()
    winners = bruteforce.solve(tournament)
    bft = time.perf_counter() - start
    print(f"BF: {winners} in {bft}")

start = time.perf_counter()
result = sat.solve_one(tournament, v_star)
satt = time.perf_counter() - start
print(f"\nSAT: {result} in {satt}")

start = time.perf_counter()
dpr = dp.solve_one(tournament, v_star)
dpt = time.perf_counter() - start
print(f"DP: {dpr} in {dpt}")

print(satt / dpt)

start = time.perf_counter()
oldr = sat.solve_one(tournament, v_star, improvement=False)
oldt = time.perf_counter() - start
print(f"\nSAT (old): {oldr} in {oldt}")

print(ln, v_star, feedback, satt, dpt, oldt, sep="; ")
