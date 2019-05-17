# In case the Makefile doesn't work for you, try this script.

g++ -ggdb -lz -D DEBUG -O3 Main.C Solver.C Constraints.C -o minisat
