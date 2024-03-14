import sys
import matplotlib.pyplot as plt
import numpy as np

with open(sys.argv[1], "r") as f:
    times1 = []
    times1d = []
    ixs1 = []
    times1b = []
    times1bd = []
    ixs1b = []
    ix = 0

    last = None
    for line in f:
        if line.startswith("TIC_NEW_SUCC"):
            last2 = int(line.strip().split()[1])
            times1.append(last2)
            times1d.append(last2 - last if last is not None else 0)
            ixs1.append(ix)
            ix += 1
            last = last2
        elif line.startswith("TIC_NEXT_PRED"):
            last2 = int(line.strip().split()[1])
            times1b.append(last2)
            times1bd.append(last2 - last if last is not None else 0)
            ixs1b.append(ix)
            ix += 1
            last = last2

with open(sys.argv[2], "r") as f:
    times2 = []
    times2d = []
    ixs2 = []
    times2b = []
    times2bd = []
    ixs2b = []
    ix = 0

    last = None
    for line in f:
        if line.startswith("TIC_NEW_SUCC"):
            last2 = int(line.strip().split()[1])
            times2.append(last2)
            times2d.append(last2 - last if last is not None else 0)
            ixs2.append(ix)
            ix += 1
            last = last2
        elif line.startswith("TIC_NEXT_PRED"):
            last2 = int(line.strip().split()[1])
            times2b.append(last2)
            times2bd.append(last2 - last if last is not None else 0)
            ixs2b.append(ix)
            ix += 1
            last = last2

fig, ax1 = plt.subplots()
ax2 = ax1.twinx()

RANDOM = sys.argv[3] == "random"
if RANDOM:
    times1d = np.array(times1d)
    times2d = np.array(times2d)
    maxd = max(times1d.max(), times2d.max())
    randoms1 = maxd / 200 * (np.random.normal(size=times1d.size))
    randoms2 = maxd / 200 * (np.random.normal(size=times2d.size))

    times1d = times1d + randoms1
    times2d = times2d + randoms2

STEP = 300
SKIP_FROM = int(sys.argv[4])

def show_shuffled(ax, scale, *datasets):
    datasets2 = []
    for ixs, times, meta in datasets:
        ixstimes = list(zip(ixs, times))
        np.random.shuffle(ixstimes)
        for start in range(STEP):
            if start > SKIP_FROM:
                continue
            ixs_part, times_part = zip(*[ixstimes[i] for i in range(start, len(times), STEP)])
            datasets2.append((ixs_part, times_part, meta))

    np.random.shuffle(datasets2)
    for ixs_part, times_part, kwargs in datasets2:
        ax.scatter(ixs_part, np.array(times_part) * scale, **kwargs)

show_shuffled(
    ax1, 1e-6,
    (ixs1[1:], times1d[1:], dict(marker="o", s=30, color="lightgreen")),
    (ixs2[1:], times2d[1:], dict(marker="o", s=30, color="#ffaaff")),
)
show_shuffled(
    ax1, 1e-6,
    (ixs1b, times1bd,  dict(marker="o", s=2, color="green")),
    (ixs2b, times2bd,  dict(marker="o", s=2, color="magenta")),
)
show_shuffled(
    ax2, 1e-9,
    (ixs1[1:], times1[1:], dict(marker="o", s=30, color="lightblue")),
    (ixs2[1:], times2[1:], dict(marker="o", s=30, color="#ff8888")),
)
show_shuffled(
    ax2, 1e-9,
    (ixs1b, times1b,  dict(marker="o", s=2, color="blue")),
    (ixs2b, times2b,  dict(marker="o", s=2, color="red")),
)

legend_points = (
    ax1.scatter([], [], label="trie UNSAT", marker="o", s=30, color="lightgreen"),
    ax1.scatter([], [], label="clausal UNSAT", marker="o", s=30, color="#ffaaff"),
    ax1.scatter([], [], label="trie SAT", marker="o", s=2, color="green"),
    ax1.scatter([], [], label="clausal SAT", marker="o", s=2, color="magenta"),
    ax1.scatter([], [], label="trie UNSAT accumulative", marker="o", s=30, color="lightblue"),
    ax1.scatter([], [], label="clausal UNSAT accumulative", marker="o", s=30, color="#ff8888"),
    ax1.scatter([], [], label="trie SAT accumulative", marker="o", s=2, color="blue"),
    ax1.scatter([], [], label="clausal SAT accumulative", marker="o", s=2, color="red"),
)

FONT = "Alfios"

ax1.set_xlabel("predecessor query order", fontsize=20, fontdict={"fontname": FONT})
ax1.set_ylabel("solving duration [ms]", fontsize=20, fontdict={"fontname": FONT})
ax2.set_ylabel("accumulative solving time [s]", fontsize=20, fontdict={"fontname": FONT})

if len(sys.argv) > 5:
    outpath = sys.argv[5]
    plt.title(sys.argv[6], fontsize=20, fontdict={"fontname": FONT})
    if "legend" in outpath:
        legend_fig = plt.figure()
        legend_fig.legend(
            handles=legend_points,
            loc="center",
            frameon=False,
            prop={"family": FONT, "size": 13},
        )
        legend_fig.savefig(outpath, format="pdf", bbox_inches="tight")
    else:
        plt.savefig(outpath, format="pdf", bbox_inches="tight")
else:
    plt.legend(handles=legend_points, prop={"family": FONT, "size": 13})
    plt.show()
