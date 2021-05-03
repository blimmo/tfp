from collections import defaultdict

import matplotlib.pyplot as plt
import numpy as np

def conv(s):
    try:
        return float(s)
    except ValueError:
        return np.NaN

def draw(filename, axs, title):
    sat = defaultdict(list)
    dp = defaultdict(list)
    old = defaultdict(list)
    with open(filename) as f:
        next(f)  # first line names columns
        for line in f:
            line = line.strip()
            if line == "#":
                break
            splits = line.split(";")
            if len(splits) != 6:
                continue
            ln, satt, dpt, oldt = int(splits[0]), conv(splits[3]), conv(splits[4]), conv(splits[5])
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
        axs.errorbar(x, y, yerr=[miny, maxy], label=label, capsize=3, capthick=2)

    axs.set_yscale("log")
    axs.set_ylabel("Run time (seconds)")
    axs.set_title(title)
    axs.legend()


if __name__ == "__main__":
    fig, (ax1, ax2) = plt.subplots(2, 1, sharex=True)
    draw("constant3/true.txt", ax1, title="True")
    draw("constant3/false.txt", ax2, title="False")
    ax2.set_xlabel("log(n)")
    ax2.set_xticks([2, 3, 4, 5, 6, 7])
    plt.show()
