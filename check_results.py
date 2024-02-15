import sys

for i, line in enumerate(sys.stdin):
    words = line.strip().split(" ")
    if "EMPTY" in words and "NOT_EMPTY" in words:
        print(f"INCONSISTENCY: {i} {line}")

    if "SAT" in words and "UNSAT" in words:
        print(f"INCONSISTENCY: {i} {line}")

    if "CalledProcessError" in words:
        print(f"ERROR: {i} {line}")
    else:
        for word in words:
            if word not in ("TimeoutExpired", "TimeoutError", "EMPTY", "NOT_EMPTY", "SAT", "UNSAT"):
                print(f"ERROR2: {i} {line}")
