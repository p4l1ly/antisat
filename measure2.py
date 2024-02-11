import subprocess
import sys
import time

times_f = open("times.csv", "w")
results_f = open("results.csv", "w")

for i in range(1, 13001, 52):
    for j in range(243):
        print(f"{i}\t{j}", end="\t")
        tic = time.time()
        try:
            with open(f"../data/ltl1/outputs/{i}.antisat", "r") as f:
                p = subprocess.run(
                    f"./build{j}/triesat",
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

    print(file=results_f)
    print(file=times_f)
