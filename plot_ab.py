import sys

import matplotlib.pyplot as plt
import numpy as np


print("PARSE")
with open(sys.argv[1], "r") as f:
    lines_a = [
        float(others[-1])
        for lix, line in enumerate(f)
        if line.count(" ") > 1
        for ix, result, *others in (line.strip().split(),)
    ]

with open(sys.argv[2], "r") as f:
    lines_b = [
        float(others[-1])
        for lix, line in enumerate(f)
        if line.count(" ") > 1
        for ix, result, *others in (line.strip().split(),)
    ]

lines = list(zip(lines_a, lines_b))

print("MAX")
if len(sys.argv) < 4:
    max_ab = max(x for ab in lines for x in ab if x != np.inf)
else:
    max_ab = float(sys.argv[3])

inf_line = max_ab * 1.15

print("SET_MAX", max_ab, inf_line)
lines = [[x if x <= max_ab else inf_line for x in xs] for xs in lines]

print("ARR")
xy = np.array(lines).T

x = xy[0]
y = xy[1]
ixs = np.array(range(len(x)), dtype=int)

print("FILTER")
fltr = (x > 0.3) | (y > 0.3)
x = x[fltr]
y = y[fltr]
ixs = ixs[fltr]

fltr2 = (x < 3) & (y > 7)
print(x[fltr2], y[fltr2], ixs[fltr2])

print("APPLY_RAND")
rands = max_ab / 60 * (np.random.multivariate_normal((0, 0), [[1, 0], [0, 1]], x.size))
x += rands[:, 0]
y += rands[:, 1]

print("PLOT")
fig, ax = plt.subplots()
del fig
plt.xlim([x.min(), max(inf_line, x.max())])
plt.ylim([y.min(), max(inf_line, y.max())])
ax.set_aspect(1)
plt.scatter(x, y, s=6, zorder=1, alpha=0.4)
plt.plot([0, max_ab], [0, max_ab], linewidth=1, color="lightgrey", zorder=0)
plt.plot([0, 0], [0, max_ab], linewidth=1, color="lightgrey", zorder=0)
plt.plot([0, max_ab], [0, 0], linewidth=1, color="lightgrey", zorder=0)
plt.plot([max_ab, max_ab], [0, max_ab], linewidth=1, color="lightgrey", zorder=0)
plt.plot([0, max_ab], [max_ab, max_ab], linewidth=1, color="lightgrey", zorder=0)
plt.show()
