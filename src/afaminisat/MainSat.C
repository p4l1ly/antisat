#include "CellContainer.h"
#include "Solver.h"
#include "Constraints.h"
#include "Trie.h"

#include <ctime>
#include <unistd.h>
#include <signal.h>
#include <iostream>
#include <sstream>
#include <vector>
#include <string>
#include <algorithm>
#include <fcntl.h>
#include <iterator>
#include <lzma.h>

using std::cout;
using std::cerr;
using std::endl;
using std::vector;
using std::string;

#ifdef MY_DEBUG
int verbosity = 5;
#endif
const bool write_debug_dots = true;

bool parse_dimacs(
  Solver& S,
  vector<Horline> &horlines,
  vector<Head*> &verlines,
  vector<Clause*> &clauses_ww
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

  S.initVars(nVars);

#ifdef TRIE_FOR_INPUT
  vec<char> mask;
  mask.growTo(S.nVars(), 0);

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

      if (!S.trie.add_clause(lits, S, S.nConstrs, sharing_set, horlines, verlines, mask)) return false;
      ++S.nConstrs;
      lits.clear();
      --nClauses;

      if (nClauses % 50000 == 0) {
        cerr << "PARSED_CLAUSES_TRIE " << nClauses << endl << std::flush;
      }
    } else {
      lits.emplace_back(abs(n) - 1, n < 0);
    }
  }

  for (Horline &horline: horlines) {
    for (Head &verhead: horline.elems) {
      verhead.above = horline.above;
    }
  }

#else

  vec<Lit> lits;

  while (nClauses) {
    int n;
    std::cin >> n;
    if (n == 0) {
      S.addClause(lits, clauses_ww);
      if (!S.okay()) return false;

      lits.clear();
      --nClauses;

      if (nClauses % 1000000 == 0) {
        cerr << "PARSED_CLAUSES " << nClauses << endl << std::flush;
      }
    } else {
      lits.push(Lit(abs(n) - 1, n < 0));
    }
  }

#endif

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


bool run() {
  vector<Horline> horlines;
  vector<Head*> verlines;
  vector<Clause*> clauses_ww;
  bool result = false;
  Head *solid = NULL;

  {
    Solver S;
    cerr << "PARSE" << endl;
    if (!parse_dimacs(S, horlines, verlines, clauses_ww)) goto dealloc;

#ifdef SOLIDIFY
    cerr << "SOLIDIFY" << endl;
    solid = S.trie.solidify();
    cerr << "TRIE_SIZE " << S.trie.count() << endl;
    vector<Horline>().swap(horlines);
    for (Head *verline: verlines) delete[] verline;
    vector<Head*>().swap(verlines);
#endif

    vector<int> order;
    order.reserve(S.nVars());
    for (int i = 0; i < S.nVars(); ++i) order.push_back(i);

#ifdef HEAP_VARORDER
    S.heap_order.init(order);
#endif

#ifdef BUBBLE_VARORDER
    S.bubble_order.init(order);
#endif

#ifdef WATCH_VARORDER
    S.watch_order.init(order);
#endif

#ifdef WATCH_CLAUSE_WATCH
    for (Clause *clause: clauses_ww) {
      S.watch_on(clause->data[0]);
    }
#endif
    vector<Clause*>().swap(clauses_ww);

    cerr << "SOLVING" << endl;
    if (verbosity >= -3) printf("SOLVING\n");

#ifdef USE_TRIE
    if (verbosity >= 2) {
      S.trie.print_guards(S);
      if (write_debug_dots) S.trie.to_dot(S, "debug/trie0.dot");
    }
#endif

    vec<Lit> empty_vec;
    if (S.solve(empty_vec)) {
      if (verbosity >= -3) printf("SOLVING_RESUME\n");

#ifdef USE_TRIE
      if (verbosity >= 2) S.trie.print_guards(S);
#endif

      result = S.resume();
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

    if (run()) {
        std::cout << "SAT" << std::endl;
    } else {
        std::cout << "UNSAT" << std::endl;
    }
}
