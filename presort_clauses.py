from collections import Counter
import sys

headers = []

counter = Counter()
clauses = []

clause = []

for line in sys.stdin:
    if line[0] in "pc":
        headers.append(line)
        continue

    words = line.strip().split()

    for word in words:
        if word == "0":
            clauses.append(clause)
            for lit in clause:
                counter[lit] += 1
            clause = []
        else:
            clause.append(word)

for header in headers:
    print(header, end="")

for clause in clauses:
    clause.sort(key=lambda x: -counter[x])
    print(*clause, 0)

