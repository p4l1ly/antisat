import sys
from collections import defaultdict
from itertools import count, cycle

import matplotlib.pyplot as plt
import numpy as np


def let(x):
    del x
    return True


print("PARSE")

with open(sys.argv[1], "r") as f:
    times = [[float(t) for t in line.strip().split()] for line in f]
with open(sys.argv[2], "r") as f:
    results = [[r for r in line.strip().split()] for line in f]
with open(sys.argv[3], "r") as f:
    tagss = [[r for r in line.strip().split()] for line in f]

constr1 = [
    clause.split(",") for clause in (sys.argv[5].split(':') if sys.argv[5] else ())
]
constr2 = [
    clause.split(",") for clause in (sys.argv[6].split(':') if sys.argv[6] else ())
]
common = [
    [clause.split(",") for clause in clauses.split(':')]
    for clauses in (sys.argv[7].split('_') if sys.argv[7] else ())
]

columns1 = [
    i
    for i, tags in enumerate(tagss)
    if all(any(tag == lit for tag in tags for lit in clause) for clause in constr1)
]
columns2 = [
    i
    for i, tags in enumerate(tagss)
    if all(any(tag == lit for tag in tags for lit in clause) for clause in constr2)
]

common_mask1 = [
    tuple(
        all(any(tag == lit for tag in tagss[i] for lit in clause) for clause in clauses)
        for clauses in common
    )
    for i in columns1
]
common_mask2 = [
    tuple(
        all(any(tag == lit for tag in tagss[i] for lit in clause) for clause in clauses)
        for clauses in common
    )
    for i in columns2
]

SHAPES = ["o", "v", "^", "<", ">", "1", "2", "3", "4", "s", "p", "P", "*", "+", "x", "X", "D", "d"]
COLORS = ["b", "g", "r", "c", "m", "y"]

print()
for shape, i in zip(cycle(SHAPES), columns1):
    print(shape, i, *tagss[i])
print()
for color, i in zip(cycle(COLORS), columns2):
    print(color, i, *tagss[i])
print()

inf_line = 1

print("MAX")

if sys.argv[4] == "-":
    max_ab = max(
        (
            tcols[i]
            for rcols, tcols in zip(results, times)
            if len(rcols) == len(tcols) == len(results[0])
            for columns in (columns1, columns2)
            for i in columns
            if rcols[i] in ("SAT", "UNSAT", "EMPTY", "NOT_EMPTY")
        ),
        default=1,
    )
else:
    max_ab = float(sys.argv[4])

inf_line = max_ab * 1.15

def score(r, t):
    if r in ("SAT", "UNSAT", "EMPTY", "NOT_EMPTY") and t <= max_ab:
        return t
    else:
        return inf_line

print("POINTS")

points = []

for k, (rcols, tcols) in enumerate(zip(results, times)):
    if not len(rcols) == len(tcols) == len(results[0]):
        continue
    bests1 = defaultdict(lambda: (np.inf, -1))
    for ii, i, mask in zip(count(), columns1, common_mask1):
        score_ = score(rcols[i], tcols[i])
        if bests1[mask][0] > score_:
            bests1[mask] = score_, ii

    bests2 = defaultdict(lambda: (np.inf, -1))
    for ii, i, mask in zip(count(), columns2, common_mask2):
        score_ = score(rcols[i], tcols[i])
        if bests2[mask][0] > score_:
            bests2[mask] = score_, ii

    for mask1, (score1, i) in bests1.items():
        if bests2.get(mask1) is not None:
            score2, j = bests2[mask1]
            if score1 < 2 and score2 > 15 or score1 < 20 and score2 > 20 or score1 > 5 and score1 < 10:
                print((columns1[i], columns2[j], k, score1, score2))
            points.append((score1, score2, SHAPES[i % len(SHAPES)], COLORS[j % len(COLORS)]))

print("PARTITION", len(points))

# partition points by style, which is a tuple of shape and color
points_by_style = defaultdict(list)
for x, y, shape, color in points:
    points_by_style[(shape, color)].append((x, y))

print("PLOT", len(points_by_style))

fig, ax = plt.subplots()
del fig

xmin = 0
ymin = 0
xmax = inf_line
ymax = inf_line

for (shape, color), points in points_by_style.items():
    xy = np.array(points).T

    x = xy[0]
    y = xy[1]
    ixs = np.array(range(len(x)), dtype=int)

    # fltr = (x > 0.3) | (y > 0.3)
    # if not fltr.any():
    #     continue

    # x = x[fltr]
    # y = y[fltr]
    # ixs = ixs[fltr]

    rands = max_ab / 60 * (np.random.multivariate_normal((0, 0), [[1, 0], [0, 1]], x.size))
    xr = x + rands[:, 0]
    yr = y + rands[:, 1]

    xmin = min(xmin, xr.min())
    ymin = min(ymin, yr.min())
    xmax = max(xmax, xr.max())
    ymax = max(ymax, yr.max())

    plt.scatter(x, y, s=10, zorder=2, color="black")
    plt.scatter(xr, yr, s=20, zorder=1, alpha=0.3, marker=shape, color=color)


plt.xlim([xmin, xmax])
plt.ylim([ymin, xmax])
ax.set_aspect(1)
plt.plot([0, max_ab], [0, max_ab], linewidth=1, color="lightgrey", zorder=0)
plt.plot([0, 0], [0, max_ab], linewidth=1, color="lightgrey", zorder=0)
plt.plot([0, max_ab], [0, 0], linewidth=1, color="lightgrey", zorder=0)
plt.plot([max_ab, max_ab], [0, max_ab], linewidth=1, color="lightgrey", zorder=0)
plt.plot([0, max_ab], [max_ab, max_ab], linewidth=1, color="lightgrey", zorder=0)

plt.show()
