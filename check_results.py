import re
import sys

success_counts = None

for i, line in enumerate(sys.stdin):
    words = line.strip().split(" ")

    if success_counts is None:
        success_counts = [0] * len(words)

    if len(words) == len(success_counts):
        for i, word in enumerate(words):
            if word in ("EMPTY", "NOT_EMPTY", "SAT", "UNSAT"):
                success_counts[i] += 1

    if "EMPTY" in words and "NOT_EMPTY" in words:
        print(f"INCONSISTENCY: {i} {line}")

    if "SAT" in words and "UNSAT" in words:
        print(f"INCONSISTENCY: {i} {line}")

    if "CalledProcessError" in words:
        print(f"ERROR: {i} {line}")
    else:
        for word in words:
            if word not in ("TimeoutExpired", "TimeoutError", "EMPTY", "NOT_EMPTY", "SAT", "UNSAT", "OK"):
                print(f"ERROR2: {i} {line}")

assert success_counts is not None

if len(sys.argv) > 1:
    tags = []
    regex = re.compile(sys.argv[2])
    with open(sys.argv[1], "r") as f:
        for line in f:
            my_tags = []
            words = line.strip().split(" ")
            for word in words:
                if regex.match(word):
                    my_tags.append(word)
            my_tags.sort()
            tags.append(" ".join(my_tags))
else:
    tags = ["" for _ in success_counts]

table = list(zip(enumerate(success_counts), tags))
table.sort(key=lambda x: -x[0][1])
print(*table, sep="\n")
