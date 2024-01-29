from collections import Counter
import sys
import random

random.seed(sys.argv[2])

headers = []

counter = Counter()
clauses = []

clause = []

pline_found = False

for line in sys.stdin:
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
        clause_count = int(words[3])
        clause_count -= int(sys.argv[1])
        headers.append(" ".join(("p cnf", str(var_count), str(clause_count))) + "\n")
        continue

    words = line.strip().split()

    for word in words:
        if word == "0":
            clauses.append(clause)
            for lit in clause:
                counter[lit] += 1
            clause = []
        else:
            clause.append(int(word))

assert pline_found

for header in headers:
    print(header, end="")

all_vars = list(range(1, var_count + 1))
random.shuffle(all_vars)

renumbering = {}
for i, var in enumerate(all_vars, 1):
    renumbering[var] = i
    renumbering[-var] = -i

randsort = {}

for i, var in enumerate(all_vars):
    randsort[var] = i
    randsort[-var] = i

GLOBAL_SORT = False

for _, clause in zip(range(clause_count), clauses):
    clause = [renumbering[x] for x in clause]
    clause.sort(key=lambda x: (-counter[x], x) if GLOBAL_SORT else -counter[x])
    print(*clause, 0)
