import ast
import time

from graph import Graph
import sat
import bruteforce
import dp

ln = 3
feedback = [
    (0, 3),
    (3, 7),
    # (2, 5),
    # (0, 6),
    # (1, 8),
    # (1, 13),
    # (10, 12)
]
v_star = 2
# inp = "5; 27; ((0, 14), (3, 19), (6, 11))"
# ln, v_star, feedback = (ast.literal_eval(i.strip()) for i in inp.split(";")[:3])
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
