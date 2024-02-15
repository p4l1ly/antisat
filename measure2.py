import subprocess
import sys
import time

times_f = open("times.csv", "w")
results_f = open("results.csv", "w")

def measure_with(i, j, program):
    print(f"{i}\t{j}", end="\t")
    tic = time.time()
    try:
        with open(f"../data/ltl1/outputs/{i}.antisat", "r") as f:
            p = subprocess.run(
                program,
                stdin=f,
                timeout=float(sys.argv[1]),
                capture_output=True,
                check=True
            )
        result = p.stdout.decode("utf8").strip()
        print(result, end=" ", file=results_f)
    except Exception as e:
        result = e.__class__.__name__
        print(result, end=" ", file=results_f)
    print(result)
    toc = time.time()
    print(f"{toc - tic:.2f}", end=" ", file=times_f)

ANTISAT_COUNT = 243
CRYPTOMINISAT_COUNT = 6

for i in range(1, 13001, 52):
    for j in range(ANTISAT_COUNT):
        measure_with(i, j, f"./build{j}/triesat")

    # cryptominisat-antichain is too slow

    # for j in range(CRYPTOMINISAT_COUNT):
    #     measure_with(i, 243 + j, f"../cryptominisat-antichain/build{j}/cryptominisat-antichain")

    print(file=results_f)
    print(file=times_f)
