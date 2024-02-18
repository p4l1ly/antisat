from collections import Counter
import sys
import random

random.seed(sys.argv[2])

headers = []

counter = Counter()
clauses = []

clause = []

pline_found = False

with open(sys.argv[1], "r") as f:
    for i, line in enumerate(f):
        if i % 1000000 == 0:
            print(i, file=sys.stderr)

        if line[0] == "c":
            headers.append(line)
            continue

        if line[0] == "p":
            assert not pline_found
            pline_found = True

            words = line.strip().split()
            assert words[0] == "p"
            assert words[1] == "cnf"
            var_count = int(words[2])
            headers.append(line)
            continue

        words = line.strip().split()

        for word in words:
            if word == "0":
                for lit in clause:
                    counter[lit] += 1
                clause = []
            else:
                clause.append(int(word))

assert pline_found

print("headers", var_count, file=sys.stderr)
for header in headers:
    print(header, end="")

print("all_vars", var_count, file=sys.stderr)
all_vars = list(range(1, var_count + 1))
print("shuffle", file=sys.stderr)
random.shuffle(all_vars)

print("renumber", file=sys.stderr)
renumbering = [0] * 2 * (var_count + 1)
for i, var in enumerate(all_vars, 1):
    renumbering[var] = i
    renumbering[-var] = -i

GLOBAL_SORT = False

print("write", file=sys.stderr)

with open(sys.argv[1], "r") as f:
    for line in f:
        if line[0] in ("p", "c"):
            continue

        words = line.strip().split()

        for word in words:
            if word == "0":
                clause = [renumbering[x] for x in clause]
                clause.sort(key=lambda x: (-counter[x], x) if GLOBAL_SORT else -counter[x])
                print(*clause, 0)
                clause = []
            else:
                clause.append(int(word))
