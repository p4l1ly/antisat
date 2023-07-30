import sys

wrong_colcount_lines = []
inconsistent_lines = []
error_lines = []
interesting_lines = []
all_timeout_lines = []
long_lines = []
partial_timeout_lines = []

for line in sys.stdin:
    cols = line.strip().split(" ")

    if len(cols) != 25:
        wrong_colcount_lines.append(line)
        continue

    result = None
    error = False
    consistent_results = True
    has_timeout = False
    all_timeout = True
    for i in (1, 7, 13, 19):
        if cols[i] == "TIMEOUT":
            has_timeout = True
            continue
        all_timeout = False
        if cols[i] == "ERROR":
            error = True
        elif result == None:
            result = cols[i]
        elif result != cols[i]:
            consistent_results = False

    if not consistent_results:
        inconsistent_lines.append(line)
    elif error:
        error_lines.append(line)
    elif has_timeout:
        if all_timeout:
            all_timeout_lines.append(line)
        else:
            partial_timeout_lines.append(line)
    elif not all_timeout:
        times = [float(x) for x in (cols[2], cols[8], cols[14], cols[20])]
        max_time = max(times)
        min_time = min(times)
        if max_time > 1:
            long_lines.append(line)
            if min_time < max_time * 0.7:
                interesting_lines.append(line)


for name in (
    "all_timeout_lines",
    "long_lines",
    "inconsistent_lines",
    "error_lines",
    "partial_timeout_lines",
    "interesting_lines",
    "wrong_colcount_lines",
):
    print("START_SECTION", name)
    for line in locals()[name]:
        print("   ", line, end="")
