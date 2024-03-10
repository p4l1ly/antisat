import sys
from collections import defaultdict
from itertools import count, cycle

import matplotlib.pyplot as plt
import numpy as np


def let(x):
    del x
    return True


print("PARSE")

BENCHTAG_COLUMNS = (0,)

with open(sys.argv[1], "r") as f:
    times = [[float(t) for t in line.strip().split()] for line in f]
with open(sys.argv[2], "r") as f:
    results = [[r for r in line.strip().split()] for line in f]
with open(sys.argv[3], "r") as f:
    tagss = [[r for r in line.strip().split()] for line in f]
if sys.argv[4]:
    with open(sys.argv[4], "r") as f:
        benchtags = [[r for r in line.strip().split()] for line in f]
else:
    BENCHTAG_COLUMNS = ()

constr1 = [
    clause.split(",") for clause in (sys.argv[6].split(':') if sys.argv[6] else ())
]
constr2 = [
    clause.split(",") for clause in (sys.argv[7].split(':') if sys.argv[7] else ())
]
common = [
    [clause.split(",") for clause in clauses.split(':')]
    for clauses in (sys.argv[8].split('_') if sys.argv[8] else ())
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

if BENCHTAG_COLUMNS:
    color_benchtags = sorted({
        tuple(benchtag[j] for j in BENCHTAG_COLUMNS) for benchtag in benchtags
    })
    color_benchtags = dict(zip(color_benchtags, cycle(COLORS)))

    benchtags_by_color = defaultdict(list)
    for benchtag, color in color_benchtags.items():
        benchtags_by_color[color].append(benchtag)
    print(benchtags_by_color)
    benchtags_by_color = {k: "/".join((",".join(vv) for vv in v)) for k, v in benchtags_by_color.items()}
else:
    color_benchtags = {}
    benchtags_by_color = {}

print()
for shape, i in zip(cycle(SHAPES), columns1):
    print(shape, i, *tagss[i])
print()
if BENCHTAG_COLUMNS:
    for benchtag, color in color_benchtags.items():
        print(color, benchtag)
else:
    for color, i in zip(cycle(COLORS), columns2):
        print(color, i, *tagss[i])

print()
print()

inf_line = 1

print("MAX")

if sys.argv[5] == "-":
    max_ab = max(
        (
            tcols[i]
            for rcols, tcols in zip(results, times)
            if len(rcols) == len(tcols) == len(results[0])
            for columns in (columns1, columns2)
            for i in columns
            if rcols[i] in ("SAT", "UNSAT", "EMPTY", "NOT_EMPTY", "NONEMPTY")
        ),
        default=1,
    )
else:
    max_ab = float(sys.argv[5])

inf_line = max_ab * 1.15


class NotApplicable(Exception):
    pass

def score(r, t):
    if r == "NotApplicable":
        raise NotApplicable
    if r in ("SAT", "UNSAT", "EMPTY", "NOT_EMPTY", "NONEMPTY") and t <= max_ab:
        return t
    else:
        return inf_line

print("POINTS")

points = []

for k, (rcols, tcols) in enumerate(zip(results, times)):
    if not len(rcols) == len(tcols) == len(results[0]):
        continue

    try:
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

                if len(columns1) == 1:
                    if "EMPTY" in rcols or "UNSAT" in rcols:
                        shape = "v"
                    elif "NOT_EMPTY" in rcols or "SAT" in rcols:
                        shape = "o"
                    else:
                        shape = "x"
                else:
                    shape = SHAPES[i % len(SHAPES)]

                if BENCHTAG_COLUMNS:
                    color = color_benchtags[tuple(benchtags[k][l] for l in BENCHTAG_COLUMNS)]
                else:
                    color = COLORS[j % len(COLORS)]

                points.append((score1, score2, shape, color))
    except NotApplicable:
        pass

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

visited_colors = set()
colorplots = []
for (shape, color), points in sorted(
    points_by_style.items(),
    key=lambda x: (benchtags_by_color[x[0][1]] if BENCHTAG_COLUMNS else (), x[0][0]),
):
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

    plt.scatter(x, y, s=10, zorder=20, color="black")
    if BENCHTAG_COLUMNS:
        kwargs = {"label": benchtags_by_color[color]}
    else:
        kwargs = {}

    # split xr to 10 equally big parts
    for i in range(10):
        ixs = np.array(range(i, len(xr), 10), dtype=int)
        colorplot = plt.scatter(xr[ixs], yr[ixs], s=20, zorder=i + 1, alpha=0.3, marker=shape, color=color, **kwargs)
        if color not in visited_colors:
            visited_colors.add(color)
            print(color, kwargs)
            colorplots.append(colorplot)

# Shrink current axis by 20%
box = ax.get_position()
ax.set_position([box.x0, box.y0, box.width * 0.7, box.height])
# Put a legend to the right of the current axis
ax.legend(handles=colorplots, loc='center left', bbox_to_anchor=(1, 0.5))


plt.xlim([xmin, xmax])
plt.ylim([ymin, xmax])
ax.set_aspect(1)
plt.plot([0, max_ab], [0, max_ab], linewidth=1, color="lightgrey", zorder=0)
plt.plot([0, 0], [0, max_ab], linewidth=1, color="lightgrey", zorder=0)
plt.plot([0, max_ab], [0, 0], linewidth=1, color="lightgrey", zorder=0)
plt.plot([max_ab, max_ab], [0, max_ab], linewidth=1, color="lightgrey", zorder=0)
plt.plot([0, max_ab], [max_ab, max_ab], linewidth=1, color="lightgrey", zorder=0)

plt.show()
