import subprocess
import sys
import time

for i in range(1, 13001):
    print(i, end=" ")
    tic = time.time()
    try:
        with open(f"../data/ltl1/outputs/{i}.antisat", "r") as f:
            p = subprocess.run(
                "./build/triesat",
                stdin=f,
                timeout=float(sys.argv[1]),
                capture_output=True,
                check=True
            )
        # print(p.stdout.decode("utf8").split("\n")[-2].strip(), end=" ")
        print(p.stdout.decode("utf8").strip(), end=" ")
    except Exception as e:
        print(e.__class__.__name__, end=" ")
    toc = time.time()
    print(f"{toc - tic:.2f}", flush=True)

