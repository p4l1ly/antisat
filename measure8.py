import asyncio
import asyncio.subprocess
import subprocess
import os
import random
import sys
import time
import traceback
from functools import partial
from typing import Union
import numpy.random as npr
import resource

MAX_VIRTUAL_MEMORY = 10 * 1024 * 1024 * 1024 # 10 GiB

def limit_virtual_memory():
    # The tuple below is of the form (soft limit, hard limit). Limit only
    # the soft part so that the limit can be increased later (setting also
    # the hard limit would prevent that).
    # When the limit cannot be changed, setrlimit() raises ValueError.
    resource.setrlimit(resource.RLIMIT_AS, (MAX_VIRTUAL_MEMORY, resource.RLIM_INFINITY))

PROBLEMS = [
    "../data/vlsat/vlsat2_14424_7585190.cnf",
    "../data/vlsat/vlsat2_2231_68844.cnf",
    "../data/vlsat/vlsat2_1022_14955.cnf",
    "../data/vlsat/vlsat2_27507_3314450.cnf",
    "../data/vlsat/vlsat2_35929_5082743.cnf",
    "../data/vlsat/vlsat2_21573_2289124.cnf",
    "../data/vlsat/vlsat2_14016_1374747.cnf",
    "../data/vlsat/vlsat2_29736_3780419.cnf",
    "../data/vlsat/vlsat2_26606_3191844.cnf",
    "../data/vlsat/vlsat2_600_11440.cnf",
    "../data/vlsat/vlsat2_2340_70758.cnf",
    "../data/vlsat/vlsat2_11374_1150943.cnf",
    "../data/vlsat/vlsat2_36603_5137412.cnf",
    "../data/vlsat/vlsat2_40170_5970608.cnf",
    "../data/vlsat/vlsat2_15960_1464039.cnf",
    "../data/vlsat/vlsat2_67996_13708722.cnf",
    "../data/vlsat/vlsat2_24450_2770239.cnf",
    "../data/vlsat/vlsat2_14637_1778453.cnf",
    "../data/vlsat/vlsat2_59204_10973962.cnf",
    "../data/vlsat/vlsat2_32480_4362044.cnf",
    "../data/vlsat/vlsat2_26988_3251923.cnf",
    "../data/vlsat/vlsat2_1125_15795.cnf",
    "../data/vlsat/vlsat2_11664_5532624.cnf",
    "../data/vlsat/vlsat2_46440_7369989.cnf",
    "../data/vlsat/vlsat2_41535_6200014.cnf",
    "../data/vlsat/vlsat2_58380_10775711.cnf",
    "../data/vlsat/vlsat2_23961_2714844.cnf",
    "../data/vlsat/vlsat2_1000_22250.cnf",
    "../data/vlsat/vlsat2_71816_14478832.cnf",
    "../data/vlsat/vlsat2_1560_54564.cnf",
    "../data/vlsat/vlsat2_15249_1937993.cnf",
    "../data/vlsat/vlsat2_21114_2240429.cnf",
    "../data/vlsat/vlsat2_1183_26975.cnf",
    "../data/vlsat/vlsat2_14640_1323246.cnf",
    "../data/vlsat/vlsat2_34161_4607712.cnf",
    "../data/vlsat/vlsat2_3456_192912.cnf",
    "../data/vlsat/vlsat2_31552_5400750.cnf",
    "../data/vlsat/vlsat2_45150_7165285.cnf",
    "../data/vlsat/vlsat2_736_11022.cnf",
    "../data/vlsat/vlsat2_17688_1741702.cnf",
    "../data/vlsat/vlsat2_28930_6497511.cnf",
    "../data/vlsat/vlsat2_2403_100259.cnf",
    "../data/vlsat/vlsat2_684_13953.cnf",
    "../data/vlsat/vlsat2_30195_3855554.cnf",
    "../data/vlsat/vlsat2_12690_1481522.cnf",
    "../data/vlsat/vlsat2_18250_2995915.cnf",
    "../data/vlsat/vlsat2_37758_5364539.cnf",
    "../data/vlsat/vlsat2_11130_1186888.cnf",
    "../data/vlsat/vlsat2_1155_42917.cnf",
    "../data/vlsat/vlsat2_1326_35956.cnf",
    "../data/vlsat/vlsat2_16297_1562268.cnf",
    "../data/vlsat/vlsat2_70288_14170788.cnf",
    "../data/vlsat/vlsat2_2548_119204.cnf",
    "../data/vlsat/vlsat2_20424_2157568.cnf",
    "../data/vlsat/vlsat2_69524_14016766.cnf",
    "../data/vlsat/vlsat2_22032_3022731.cnf",
    "../data/vlsat/vlsat2_29456_6615638.cnf",
    "../data/vlsat/vlsat2_5600_1042700.cnf",
    "../data/vlsat/vlsat2_5152_824642.cnf",
    "../data/vlsat/vlsat2_7452_334035.cnf",
    "../data/vlsat/vlsat2_41875_6420498.cnf",
    "../data/vlsat/vlsat2_47817_1337056.cnf",
    "../data/vlsat/vlsat2_3480_190496.cnf",
    "../data/vlsat/vlsat2_1134_26703.cnf",
    "../data/vlsat/vlsat2_5568_1124240.cnf",
    "../data/vlsat/vlsat2_1209_29889.cnf",
    "../data/vlsat/vlsat2_1586_57751.cnf",
    "../data/vlsat/vlsat2_30744_3925645.cnf",
    "../data/vlsat/vlsat2_1352_42432.cnf",
    "../data/vlsat/vlsat2_798_17543.cnf",
    "../data/vlsat/vlsat2_16788_9021307.cnf",
    "../data/vlsat/vlsat2_11280_4223777.cnf",
    "../data/vlsat/vlsat2_33582_4529625.cnf",
    "../data/vlsat/vlsat2_39552_5878762.cnf",
    "../data/vlsat/vlsat2_16269_2203672.cnf",
    "../data/vlsat/vlsat2_36792_5273558.cnf",
    "../data/vlsat/vlsat2_15704_1804650.cnf",
    "../data/vlsat/vlsat2_83334_20350783.cnf",
    "../data/vlsat/vlsat2_40896_6104639.cnf",
    "../data/vlsat/vlsat2_5525_327765.cnf",
    "../data/vlsat/vlsat2_684_9417.cnf",
    "../data/vlsat/vlsat2_68760_13862744.cnf",
    "../data/vlsat/vlsat2_21190_2597791.cnf",
    "../data/vlsat/vlsat2_26104_3131630.cnf",
    "../data/vlsat/vlsat2_33040_4437242.cnf",
    "../data/vlsat/vlsat2_29205_3712921.cnf",
    "../data/vlsat/vlsat2_19565_3665001.cnf",
    "../data/vlsat/vlsat2_708_10259.cnf",
    "../data/vlsat/vlsat2_29040_3874024.cnf",
    "../data/vlsat/vlsat2_34099_4695729.cnf",
    "../data/vlsat/vlsat2_16676_1598591.cnf",
    "../data/vlsat/vlsat2_57038_10572502.cnf",
    "../data/vlsat/vlsat2_21546_2615351.cnf",
    "../data/vlsat/vlsat2_4424_545056.cnf",
    "../data/vlsat/vlsat2_3252_372331.cnf",
    "../data/vlsat/vlsat2_14280_6781327.cnf",
    "../data/vlsat/vlsat2_15440_1409906.cnf",
    "../data/vlsat/vlsat2_544_8738.cnf",
    "../data/vlsat/vlsat2_29945_3796274.cnf",
    "../data/vlsat/vlsat2_36518_5166057.cnf",
]

TIMEOUT = float(sys.argv[1])


class TimeoutError(Exception):
    def __str__(self):
        return "TimeoutError"


class ReturnCodeError(Exception):
    def __init__(self, returncode):
        self.returncode = returncode

    def __str__(self):
        return f"ReturnCode{self.returncode}"


class NotFoundError(Exception):
    def __str__(self):
        return "NotFound"


async def check_stdin_unpacked(problem, program) -> Union[bytes, Exception]:
    try:
        with open(problem, "r") as f:
            p = await asyncio.create_subprocess_exec(
                program,
                stdin=f,
                stdout=asyncio.subprocess.PIPE,
                preexec_fn=limit_virtual_memory,
            )

            assert p.stdout is not None
            try:
                result = await asyncio.wait_for(p.stdout.read(), TIMEOUT)

                # check status code
                if await p.wait() not in (0, 10, 20):
                    return ReturnCodeError(p.returncode)

                return result
            except asyncio.TimeoutError:
                p.terminate()
                return TimeoutError()
    except FileNotFoundError:
        return NotFoundError()


def unxz(problem):
    subprocess.run(("cp", problem, "../data/unxz.cnf"), check=True)
    return "OK"


def presort_clauses(mode="global", seed="", shuffle=True, sbva=False):
    wpath = f"../data/presort{'_sbva' if sbva else ''}.cnf"
    rpath = f"../data/{'sbva' if sbva else 'unxz'}.cnf"
    try:
        with open(rpath, "r"):
            pass
    except FileNotFoundError:
        try:
            os.remove(wpath)
        except FileNotFoundError:
            pass
        return "NotFound"

    with open(wpath, "w") as f2:
        p = subprocess.Popen(
            (
                "python3",
                "presort_clauses.py",
                rpath,
                seed,
                mode,
                "shuffle" if shuffle else "noshuffle",
            ),
            stdout=f2,
        )
        ret = p.wait()
        if ret != 0:
            os.remove(wpath)
            return "NotFound"
    return "OK"


loop = asyncio.get_event_loop()


def check_antisat(problem, program):
    try:
        stdout = loop.run_until_complete(check_stdin_unpacked(problem, program))
    except Exception as e:
        return e.__class__.__name__
    if isinstance(stdout, Exception):
        return str(stdout)
    stdout_last = stdout.split(b"\n")[-2]
    if stdout_last == b"SAT":
        return "SAT"
    if stdout_last == b"UNSAT":
        return "UNSAT"
    return "UNEXPECTED"


def antisat(i, inp, build_suffix, name_suffix):
    return (
        f"antisat{name_suffix}{i}",
        lambda _: check_antisat(f"../data/{inp}.cnf", f"./buildsat{build_suffix}{i}/triesat")
    )


def check_minisat(problem, program):
    try:
        stdout = loop.run_until_complete(check_stdin_unpacked(problem, program))
    except Exception as e:
        return e.__class__.__name__
    if isinstance(stdout, Exception):
        return str(stdout)
    stdout_last = stdout.split(b"\n")[-2]
    if stdout_last == b"SATISFIABLE":
        return "SAT"
    if stdout_last == b"UNSATISFIABLE":
        return "UNSAT"
    return "UNEXPECTED"


def minisat(version, inp):
    program = f"../MiniSat_v{version}/minisat"
    return f"minisat{version}_{inp}", lambda _: check_minisat(f"../data/{inp}.cnf", program)


def check_s(check):
    try:
        stdout = loop.run_until_complete(check)
    except Exception as e:
        traceback.print_exc()
        return e.__class__.__name__
    if isinstance(stdout, Exception):
        return str(stdout)
    stdout_lines = stdout.split(b"\n")
    if b"s SATISFIABLE" in stdout_lines:
        return "SAT"
    if b"s UNSATISFIABLE" in stdout_lines:
        return "UNSAT"
    return "UNEXPECTED"


def cadical(inp):
    program = f"../cadical/build/cadical"
    return f"cadical_{inp}", lambda _: check_s(check_stdin_unpacked(f"../data/{inp}.cnf", program))


def cryptominisat(inp):
    program = f"../cryptominisat/build/cryptominisat5"
    return f"cryptominisat_{inp}", lambda _: check_s(check_stdin_unpacked(f"../data/{inp}.cnf", program))


def sbva():
    p = subprocess.run(
        (
            "../SBVA/sbva",
            "-i",
            "../data/unxz.cnf",
            "-o",
            "../data/sbva.cnf",
            "-t",
            str(int(TIMEOUT)),
        ),
        preexec_fn=limit_virtual_memory,
    )

    if p.returncode != 0:
        subprocess.call("cp ../data/unxz.cnf ../data/sbva.cnf", shell=True)
        return "SbvaError"

    return "OK"

with open("sat_small.tags", "r") as f:
    stagss = [line.strip().split() for line in f]

# TODO if we have time: presort for trie, then, maybe run all again with sbva

PROGRAMS = (
    (("unxz", unxz), ["unxz", "preprocess"]),
    (("sbva", lambda _: sbva()), ["sbva", "preprocess"]),
    (("presort", partial(presort_clauses, sbva=True, seed="gq92mgvw3ngwjb")), ["presort", "preprocess"]),
    (antisat(0, "sbva", "sh", ""), stagss[1] + ["nopresort", "antisat", "sbva", "nopreprocess"]),
    (antisat(1, "presort_sbva", "sh", "_presort"), stagss[1] + ["presort", "antisat", "sbva", "nopreprocess"]),
    # (minisat("1.12b", "sbva"), ["minisat", "1.12b", "sbva", "noantisat", "nopreprocess"]),
    # (minisat("1.14", "sbva"), ["minisat", "1.14", "sbva", "noantisat", "nopreprocess"]),
    (cadical("sbva"), ["cadical", "sbva", "noantisat", "nopreprocess"]),
)

PRINT_TAGS = False
DRY_RUN = False
WRITE_MODE = "a"

if PRINT_TAGS or DRY_RUN:
    times_f = sys.stdout
    results_f = sys.stdout
    benchtags_f = sys.stdout
else:
    times_f = open("times_vlsat.csv", WRITE_MODE)
    results_f = open("results_vlsat.csv", WRITE_MODE)
    benchtags_f = open("benchtags_vlsat.csv", WRITE_MODE)


def measure_with(problem, program, quiet=False):
    print(f"{problem}\t{program[0]}", end="\t", flush=True)
    tic = time.time()
    result = program[1](problem)
    if not quiet:
        print(result, end=" ", file=results_f, flush=True)
    toc = time.time()
    print(f"{result}\t{toc - tic:.2f}", flush=True)
    if not quiet:
        print(f"{toc - tic:.2f}", end=" ", file=times_f, flush=True)

if PRINT_TAGS:
    for (_, tags) in PROGRAMS:
        print(*tags)
else:
    rangen = npr.default_rng(seed=list(b"qveo3tj309rfkv240"))
    rangen.shuffle(PROBLEMS)
    for i, problem in enumerate(PROBLEMS, 1): # if i <= 25:
        print(problem, file=benchtags_f, flush=True)

        for j, (program, _) in enumerate(PROGRAMS, 1):
            measure_with(problem, program)

        print(file=results_f, flush=True)
        print(file=times_f, flush=True)
