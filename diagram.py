from collections import defaultdict

import matplotlib.pyplot as plt
import numpy as np

sat = defaultdict(list)
dp = defaultdict(list)
old = defaultdict(list)
with open("results.txt") as f:
    next(f)  # first line names columns
    for line in f:
        line = line.strip()
        if line == "#":
            break
        splits = line.split(";")
        if len(splits) != 6:
            continue
        ln, satt, dpt, oldt = int(splits[0]), float(splits[3]), float(splits[4]), float(splits[5])
        sat[ln].append(satt)
        dp[ln].append(dpt)
        old[ln].append(oldt)

for d, label in zip((sat, dp, old), ("SAT", "DP", "OLD")):
    x = []
    y = []
    maxy = []
    miny = []
    for k, v in d.items():
        x.append(k)
        avg = np.mean(v)
        y.append(avg)
        maxy.append(max(v) - avg)
        miny.append(avg - min(v))
    print(x, y, maxy, miny)
    plt.errorbar(x, y, yerr=[maxy, miny], label=label, capsize=3, capthick=2)

plt.yscale("log")
plt.legend()
plt.show()
