import math
import random
import subprocess
import sys
import time
import resource

# Maximal virtual memory for subprocesses (in bytes).
MAX_VIRTUAL_MEMORY = 20 * 1024 * 1024 * 1024 # 20 GiB

def limit_virtual_memory():
    # The tuple below is of the form (soft limit, hard limit). Limit only
    # the soft part so that the limit can be increased later (setting also
    # the hard limit would prevent that).
    # When the limit cannot be changed, setrlimit() raises ValueError.
    resource.setrlimit(resource.RLIMIT_AS, (MAX_VIRTUAL_MEMORY, resource.RLIM_INFINITY))

TIMEOUT = float(sys.argv[1])
SUFFIX = sys.argv[2]
ANTISAT_COUNT = int(sys.argv[3])

times_f = open(f"times_{SUFFIX}_300.csv", "a")
results_f = open(f"results_{SUFFIX}_300.csv", "a")

def measure_with(path, j, program):
    print(f"{path}\t{j}", end="\t", flush=True)
    tic = time.time()
    try:
        with open(path, "r") as f:
            p = subprocess.run(
                program,
                stdin=f,
                timeout=TIMEOUT,
                capture_output=True,
                check=True,
                preexec_fn=limit_virtual_memory,
            )
        result = p.stdout.decode("utf8").strip()
        print(result, end=" ", file=results_f, flush=True)
    except Exception as e:
        result = e.__class__.__name__
        print(result, end=" ", file=results_f, flush=True)
    print(result)
    toc = time.time()
    print(f"{toc - tic:.2f}", end=" ", file=times_f, flush=True)

random.seed("qveo3tj309rfkv240")

input_paths = subprocess.run(
    "ls ../data/afacomp_simpl_tseytin",
    shell=True,
    stdout=subprocess.PIPE,
    check=True
)
input_paths = input_paths.stdout.decode("utf8").strip().split("\n")

global_ix = 0
for input_path in input_paths:
    input_paths2 = subprocess.run(
        "ls ../data/afacomp_simpl_tseytin/" + input_path,
        shell=True,
        stdout=subprocess.PIPE,
        check=True
    )
    input_paths2 = input_paths2.stdout.decode("utf8").strip().split("\n")

    for ipath in random.sample(input_paths2, min(len(input_paths2), 300)):
        global_ix += 1
        if global_ix < 1795:
            continue
        ipath = f"../data/afacomp_simpl_tseytin/{input_path}/{ipath}"
        for j in range(ANTISAT_COUNT):
            measure_with(ipath, j, f"./buildafa_{SUFFIX}{j}/triesat")

        print(file=results_f, flush=True)
        print(file=times_f, flush=True)
