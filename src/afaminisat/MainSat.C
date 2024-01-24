/**************************************************************************************************
MiniSat -- Copyright (c) 2003-2005, Niklas Een, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include "SupQ.h"
#include "CellContainer.h"
#include "Solver.h"
#include "Constraints.h"
#include "Trie.h"

#include <ctime>
#include <unistd.h>
#include <signal.h>
#include <chrono>
#include <iostream>
#include <vector>
#include <string>
#include <algorithm>
#include <fcntl.h>
#include <iterator>
#include <lzma.h>

using std::cout;
using std::endl;
using std::vector;
using std::string;
namespace chrono = std::chrono;

#ifdef MY_DEBUG
int verbosity = 5;
#endif
const bool write_debug_dots = true;

std::pair<bool, std::vector<int>> getIntLine(bool required = true) {
  std::string line;
  if (getline(std::cin, line)) {
    std::istringstream is(line);
    return std::pair(
      true,
      std::move(std::vector<int> {std::istream_iterator<int>(is), std::istream_iterator<int>()})
    );
  }
  if (required) {
    std::cerr << "Too few lines" << std::endl;
    exit(1);
  }
  return std::pair(false, std::vector<int>());
}

bool parse_dimacs(
  Solver& S,
  vector<Horline> &horlines,
  vector<Head*> &verlines
) {
  std::string line;
  bool found_p = false;
  int nVars;
  int nClauses;
  while (true) {
    getline(std::cin, line);
    if (line[0] == 'c') continue;
    if (line[0] == 'p') {
      std::istringstream is(line);
      std::string word;
      is >> word >> word >> nVars >> nClauses;
      if (verbosity >= 2) std::cout << "HEADER " << nVars << " " << nClauses << endl;
      break;
    }
    std::cerr << "Expected p or c line.\n"; exit(1);
  }

  if (GUESS_WITH_TRIE) S.pures.growTo(nVars, true);
  else S.pures.growTo(nVars, false);

  for (int i = nVars; i; --i) S.newVar();

  if (TRIE_MODE == clauses) {
    vec<Lit> lits;

    while (nClauses) {
      int n;
      std::cin >> n;
      if (n == 0) {
        S.addClause(lits);
        if (!S.okay()) return false;

        lits.clear();
        --nClauses;
      } else {
        lits.push(Lit(abs(n) - 1, n < 0));
      }
    }
  } else {
    vector<Lit> lits;
    vector<unsigned> sharing_set;
    sharing_set.resize(S.watches.size(), 0);

    while (nClauses) {
      int n;
      std::cin >> n;
      if (n == 0) {
        if (verbosity >= 2) {
          std::cout << "ADD_CLAUSE " << S.nConstrs;
          for (Lit lit: lits) cout << " " << lit;
          cout << endl;
        }

        if (!S.trie.add_clause(lits, S, S.nConstrs, sharing_set, horlines, verlines)) return false;
        ++S.nConstrs;
        lits.clear();
        --nClauses;
      } else {
        lits.emplace_back(abs(n) - 1, n < 0);
      }
    }

    for (Horline &horline: horlines) {
      for (Head &verhead: horline.elems) {
        verhead.above = horline.above;
      }
    }

    cout << "TRIE_SIZE " << S.trie.count() << endl;
  }

  return true;
}

//=================================================================================================


void printStats(SolverStats& stats, double cpu_time)
{
    printf("restarts              : %" I64_fmt "\n", stats.starts);
    printf("conflicts             : %-12" I64_fmt "   (%.0f /sec)\n", stats.conflicts   , stats.conflicts   /cpu_time);
    printf("decisions             : %-12" I64_fmt "   (%.0f /sec)\n", stats.decisions   , stats.decisions   /cpu_time);
    printf("propagations          : %-12" I64_fmt "   (%.0f /sec)\n", stats.propagations, stats.propagations/cpu_time);
    printf("inspects              : %-12" I64_fmt "   (%.0f /sec)\n", stats.inspects    , stats.inspects    /cpu_time);
    printf("CPU time              : %g s\n", cpu_time);
}

Solver* solver;
static void SIGINT_handler(int signum) {
    printf("\n"); printf("*** INTERRUPTED ***\n");
    printStats(solver->stats, cpuTime());
    printf("\n"); printf("*** INTERRUPTED ***\n");
    exit(0); }


//=================================================================================================


bool run(char mode) {
  vector<Horline> horlines;
  vector<Head*> verlines;
  bool result = false;
  Head *solid = NULL;

  {
    Solver S;
    switch (mode) {
      case '0':
        TRIE_MODE = clauses;
        GUESS_WITH_TRIE = false;
        break;
      case '1':
        TRIE_MODE = branch_always;
        GUESS_WITH_TRIE = false;
        break;
      case '2':
        TRIE_MODE = clauses;
        GUESS_WITH_TRIE = true;
        break;
      case '3':
        TRIE_MODE = branch_always;
        GUESS_WITH_TRIE = true;
        break;
      default:
        std::cerr << "Error: unknown mode.\n";
        exit(1);
        break;
    }
    if (!parse_dimacs(S, horlines, verlines)) goto dealloc;

    solid = S.trie.solidify();

    S.order.init();

    S.status = Solver_RUNNING;
    S.tic = chrono::steady_clock::now();

    if (verbosity >= -3) printf("SOLVING\n");
    if (verbosity >= 2) {
      S.trie.print_guards(S);
      if (write_debug_dots) S.trie.to_dot(S, "debug/trie0.dot");
    }

    vec<Lit> empty_vec;
    if (S.solve(empty_vec)) {
      if (verbosity >= -3) printf("SOLVING_RESUME\n");
      if (verbosity >= 2) S.trie.print_guards(S);
      bool result = S.resume();
      printStats(S.stats, cpuTime());
    }
  }

dealloc:
  if (solid != NULL) delete[] solid;
  for (Head *verline: verlines) delete[] verline;
  return result;
}

int main(int argc, char** argv) {
    srand(1345719);
    char mode = '3';
    if (argc >= 2) mode = argv[1][0];

    if (run(mode)) {
        std::cout << "SAT" << std::endl;
    } else {
        std::cout << "UNSAT" << std::endl;
    }
}
