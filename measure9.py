import re
import subprocess
import sys
import time
import resource
from functools import partial
from collections import defaultdict

MAX_VIRTUAL_MEMORY = 10 * 1024 * 1024 * 1024 # 10 GiB
EARLY_TEST = False
DRY_RUN = False
TIMEOUT = float(sys.argv[1])

def limit_virtual_memory():
    # The tuple below is of the form (soft limit, hard limit). Limit only
    # the soft part so that the limit can be increased later (setting also
    # the hard limit would prevent that).
    # When the limit cannot be changed, setrlimit() raises ValueError.
    resource.setrlimit(resource.RLIMIT_AS, (MAX_VIRTUAL_MEMORY, resource.RLIM_INFINITY))


if EARLY_TEST:
    BENCHDIR = "../data"
    SUFFIX_ANTISAT = "afa"
    SUFFIX_SMV = "afa"
    SUFFIX_AIG = "afa"
else:
    BENCHDIR = "../afacomp"
    SUFFIX_ANTISAT = "antisat"
    SUFFIX_SMV = "smv"
    SUFFIX_AIG = "aig"

if DRY_RUN:
    times_f = sys.stdout
    results_f = sys.stdout
    benchtags_f = sys.stdout
else:
    times_f = open(f"times9.csv", "w")
    results_f = open(f"results9.csv", "w")
    benchtags_f = open(f"benchtags9.csv", "w")


def tool_mata(sim, group, instance):
    ipath = f"{BENCHDIR}/afacomp_emp/{group}/{instance}"
    emp = f"{ipath}.emp"
    with open(emp, "r") as f:
        skip = f.read() == ""

    if skip:
        print("NotApplicable", end=" ", file=results_f, flush=True)
        print("0.0", end=" ", file=times_f, flush=True)
    else:
        nfas = subprocess.run(
            f"ls {ipath}.nfas | sort -n",
            shell=True,
            stdout=subprocess.PIPE,
            check=True
        )
        nfas = nfas.stdout.decode("utf8").strip().split("\n")
        nfas = [f"{ipath}.nfas/{nfa}" for nfa in nfas]

        tic = time.time()
        try:
            sim = " --sim" if sim else ""
            print(f"../nfa-program-parser/build/src/cpp/mata-emp-interpreter {emp}{sim} {' '.join(nfas)}")
            p = subprocess.run(
                f"../nfa-program-parser/build/src/cpp/mata-emp-interpreter {emp}{sim} {' '.join(nfas)}",
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
                result = "NOT_EMPTY"
            else:
                result = "WEIRD"
            print(result, end=" ", file=results_f, flush=True)
        except subprocess.CalledProcessError as e:
            print("STDOUT", e.stdout.decode(), sep="\n", end="\n\n")
            print("STDERR", e.stderr.decode(), sep="\n", end="\n\n")
            if e.returncode == 255 and "std::bad_alloc" in e.stderr.decode():
                print((result := "BadAlloc"), end=" ", file=results_f, flush=True)
            else:
                print((result := f"CalledProcessError{e.returncode}"), end=" ", file=results_f, flush=True)
        except Exception as e:
            import traceback
            traceback.print_exc()
            result = e.__class__.__name__
            print(result, end=" ", file=results_f, flush=True)
        toc = time.time()
        print(f"{result}\t{toc - tic:.2f}")
        print(f"{toc - tic:.2f}", end=" ", file=times_f, flush=True)


def tool_antisat(program, group, instance):
    if program in ("./buildafa_trie/triesat", "./buildafa_trie_heap_solo/triesat"):
        print("NotApplicable", end=" ", file=results_f, flush=True)
        print("0.0", end=" ", file=times_f, flush=True)
        return

    path = f"{BENCHDIR}/afacomp_simpl_tseytin/{group}/{instance}.{SUFFIX_ANTISAT}"
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
    except subprocess.CalledProcessError as e:
        print("STDOUT", e.stdout.decode(), sep="\n", end="\n\n")
        print("STDERR", e.stderr.decode(), sep="\n", end="\n\n")
        print((result := f"CalledProcessError{e.returncode}"), end=" ", file=results_f, flush=True)
    except Exception as e:
        import traceback
        traceback.print_exc()
        result = e.__class__.__name__
        print(result, end=" ", file=results_f, flush=True)
    toc = time.time()
    print(f"{result}\t{toc - tic:.2f}")
    print(f"{toc - tic:.2f}", end=" ", file=times_f, flush=True)


def tool_abc(group, instance):
    path = f"{BENCHDIR}/afacomp_simpl_aig/{group}/{instance}.{SUFFIX_AIG}"
    tic = time.time()
    try:
        with open(path, "r") as f:
            p = subprocess.run(
                (
                    "./build/abc",
                    "-c",
                    f"read_aiger {path}; drw; rf; b; drw; rwz; b; rfz; rwz; b; pdr -T {TIMEOUT}"
                ),
                stdin=f,
                timeout=TIMEOUT,
                capture_output=True,
                preexec_fn=limit_virtual_memory,
                cwd="../abc"
            )
        result = p.stdout.decode("utf8")
        if p.returncode in (124, 134):
            print(f"Timeout{p.returncode}", end=" ", file=results_f, flush=True)
        else:
            if "Output" in result:
                print((result := "NOT_EMPTY"), end=" ", file=results_f, flush=True)
            elif "prove" in result:
                print((result := "EMPTY"), end=" ", file=results_f, flush=True)
            elif p.returncode != 0:
                print((result := f"CalledProcessError{p.returncode}"), end=" ", file=results_f, flush=True)
            else:
                print("STDOUT")
                print(result)
                print("STDERR")
                print(p.stderr.decode("utf8"))
                print((result := "WEIRD"), end=" ", file=results_f, flush=True)
    except Exception as e:
        import traceback
        traceback.print_exc()
        result = e.__class__.__name__
        print(result, end=" ", file=results_f, flush=True)
    toc = time.time()
    print(f"{result}\t{toc - tic:.2f}")
    print(f"{toc - tic:.2f}", end=" ", file=times_f, flush=True)


NUXMV_REGEX_NONEMPTY = re.compile(r"^-- invariant.*is false", re.M)
NUXMV_REGEX_EMPTY = re.compile(r"^-- invariant.*is true", re.M)

def tool_nuxmv(group, instance):
    path = f"{BENCHDIR}/afacomp_simpl_smv/{group}/{instance}.{SUFFIX_SMV}"
    tic = time.time()
    try:
        with open("/tmp/nuxmv_script", "w") as f:
            print(f"read_model -i {path}", file=f)
            print("go", file=f)
            print("convert_property_to_invar", file=f)
            print("build_boolean_model", file=f)
            print("check_invar_ic3", file=f)
            print("quit", file=f)

        with open(path, "r") as f:
            p = subprocess.run(
                (
                    "../nuXmv-2.0.0-Linux/bin/nuXmv",
                    "-pre",
                    "cpp m4",
                    "-dcx",
                    "-source",
                    "/tmp/nuxmv_script",
                ),
                stdin=f,
                timeout=TIMEOUT,
                capture_output=True,
                preexec_fn=limit_virtual_memory,
            )
        result = p.stdout.decode("utf8")
        if p.returncode in (124, 134):
            print((result := f"Timeout{p.returncode}"), end=" ", file=results_f, flush=True)
        else:
            if NUXMV_REGEX_NONEMPTY.search(result):
                print((result := "NOT_EMPTY"), end=" ", file=results_f, flush=True)
            elif NUXMV_REGEX_EMPTY.search(result):
                print((result := "EMPTY"), end=" ", file=results_f, flush=True)
            elif p.returncode != 0:
                print((result := f"CalledProcessError{p.returncode}"), end=" ", file=results_f, flush=True)
            else:
                print("STDOUT")
                print(result)
                print("STDERR")
                print(p.stderr.decode("utf8"))
                print((result := "WEIRD"), end=" ", file=results_f, flush=True)
    except Exception as e:
        import traceback
        traceback.print_exc()
        result = e.__class__.__name__
        print(result, end=" ", file=results_f, flush=True)
    toc = time.time()
    print(f"{result}\t{toc - tic:.2f}")
    print(f"{toc - tic:.2f}", end=" ", file=times_f, flush=True)


TOOLS = (
    ("antisat_trie_heap_reverseadd", partial(tool_antisat, "./buildafa_trie_heap_reverseadd/triesat")),
    ("antisat_trie_heap_setsuccone", partial(tool_antisat, "./buildafa_trie_heap_setsuccone/triesat")),
)

groups = defaultdict(list)

with open("trie_good_hard.csv", "r") as f:
    for line in f:
        _ix, trie_result, trie_time, group, instance = line.strip().split(" ")
        del _ix
        groups[group].append((trie_result, trie_time, int(instance)))

groups = [(group, iter(ipaths)) for group, ipaths in groups.items()]

global_ix = 0
end = False
while not end:
    end = True
    for input_path, ipaths in groups:
        try:
            trie_result, trie_time, ipath = next(ipaths)
        except StopIteration:
            continue
        end = False

        global_ix += 1

        print(input_path, ipath, file=benchtags_f, flush=True)
        print("MEASURE", global_ix, input_path, ipath)

        print(trie_result, end=" ", file=results_f, flush=True)
        print(trie_time, end=" ", file=times_f, flush=True)

        for tool_name, tool in TOOLS:
            print(tool_name)
            tool(input_path, ipath)

        print(file=results_f, flush=True)
        print(file=times_f, flush=True)
