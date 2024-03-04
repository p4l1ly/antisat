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

times_f = open(f"times_mata_300.csv", "w")
results_f = open(f"results_mata_300.csv", "w")

def measure_with(path, nfas, sim=False):
    print(f"{path}\t{sim}", end="\t", flush=True)
    tic = time.time()
    try:
        sim = " --sim" if sim else ""
        p = subprocess.run(
            f"../nfa-program-parser/build/src/cpp/mata-emp-interpreter {path}{sim} {' '.join(nfas)}",
            timeout=TIMEOUT,
            capture_output=True,
            check=True,
            shell=True,
            preexec_fn=limit_virtual_memory,
        )
        result = p.stdout.decode("utf8")
        if "_check_result: true" in result:
            result = "EMPTY"
        elif "_check_result: false" in result:
            result = "NONEMPTY"
        else:
            result = "WEIRD"
        print(result, end=" ", file=results_f, flush=True)
    except Exception as e:
        import traceback
        traceback.print_exc()
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
        f"ls ../data/afacomp_emp/{input_path}/*.emp",
        shell=True,
        stdout=subprocess.PIPE,
        check=True
    )
    input_paths2 = input_paths2.stdout.decode("utf8").strip().split("\n")

    for ipath in random.sample(input_paths2, min(len(input_paths2), 300)):
        global_ix += 1
        # if "bool_comb" not in input_path:
        #     continue

        with open(ipath, "r") as f:
            skip = f.read() == ""

        if skip:
            print("NotApplicable NotApplicable ", file=results_f, flush=True)
            print("0.0 0.0 ", file=times_f, flush=True)
        else:
            nfas = subprocess.run(
                "ls " + ipath[:-4] + ".nfas/*",
                shell=True,
                stdout=subprocess.PIPE,
                check=True
            )
            nfas = nfas.stdout.decode("utf8").strip().split("\n")
            measure_with(ipath, nfas, sim=False)
            measure_with(ipath, nfas, sim=True)

        print(file=results_f, flush=True)
        print(file=times_f, flush=True)
