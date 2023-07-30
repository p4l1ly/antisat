import sys
import re

HEAD = object()

VALGRIND_PATTERNS = [
    re.compile("^==[0-9]+== Memcheck, a memory error detector$"),
    re.compile("^==[0-9]+== Copyright \\(C\\) 2002-2022, and GNU GPL'd, by Julian Seward et al\\.$"),
    re.compile("^==[0-9]+== Using Valgrind-3\\.21\\.0 and LibVEX; rerun with -h for copyright info$"),
    re.compile("^==[0-9]+== Command: .*$"),
    re.compile("^==[0-9]+== $"),
    re.compile("^==[0-9]+== $"),
    re.compile("^==[0-9]+== HEAP SUMMARY:$"),
    re.compile("^==[0-9]+==     in use at exit: 0 bytes in 0 blocks$"),
    re.compile("^==[0-9]+==   total heap usage: .*$"),
    re.compile("^==[0-9]+== $"),
    re.compile("^==[0-9]+== All heap blocks were freed -- no leaks are possible$"),
    re.compile("^==[0-9]+== $"),
    re.compile("^==[0-9]+== ERROR SUMMARY: 0 errors from 0 contexts \\(suppressed: 0 from 0\\)$"),
]

state = HEAD

name = None
valgrind_lines = []

try:
    for line in sys.stdin:
        if state is HEAD:
            name = line
            assert not name.startswith("==")
            state = 0
            valgrind_lines = []
        else:
            valgrind_lines.append(line)

            assert VALGRIND_PATTERNS[state].match(line)

            state += 1
            if state == 13:
                state = HEAD

except AssertionError:
    print("ERROR")
    print(state)
    print(name, end="")
    for line in valgrind_lines:
        print(line, end="")
    raise SystemExit(1)
