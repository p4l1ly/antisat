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
using std::endl;
using std::vector;
using std::string;

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


bool parse_cnfafa(
  Solver& S,
  int& acnt,
  std::vector<Lit> &all_outputs,
  vector<Clause*> &clauses_ww,
  vector<UpwardClause*> &upward_clauses_ww,
  std::unordered_set<unsigned> &finals_set
) {
  acnt = getIntLine().second[0];
  std::vector<int> outputs(std::move(getIntLine().second));
  std::vector<int> finals(std::move(getIntLine().second));
  std::vector<int> pureVars(std::move(getIntLine().second));
  std::vector<int> upwardClauses(std::move(getIntLine().second));
  std::vector<int> posqOutputs(std::move(getIntLine().second));

  int nVars = acnt + outputs.size();

  std::vector<std::vector<int>> clauses;
  while (true) {
    auto intLine = getIntLine(false);
    if (!intLine.first) break;
    clauses.push_back(std::move(intLine.second));
  }

  for (auto clause: clauses) {
    for (auto lit: clause) {
      int var = abs(lit) - 1;
      if (var + 1 > nVars) {
        nVars = var + 1;
      }
    }
  }

  S.var_types.resize(nVars, GUESS_VAR);

#ifdef NOGUESS_VARS
  for (int pure: pureVars) S.var_types[pure] = NOGUESS_VAR;
  for (unsigned i = 0; i < outputs.size(); ++i) S.var_types[i] = NOGUESS_VAR;
#endif

  unordered_set<unsigned> upwardClausesSet;
  for (auto upward: upwardClauses) upwardClausesSet.insert(upward);

  int i = 0;
  for (int output: outputs) {
    int var = abs(output) - 1;
    Lit lit = output > 0 ? Lit(var) : Lit(var, true);
    all_outputs.push_back(lit);
    VarType old_vartype = S.var_types[var];

    if (old_vartype == OUTPUT_POSNEG) S.var_types[var] = OUTPUT_POSNEG;
    else if (old_vartype == OUTPUT_POS) {
      if (output < 0) S.var_types[var] = OUTPUT_POSNEG;
    } else if (old_vartype == OUTPUT_NEG) {
      if (output > 0) S.var_types[var] = OUTPUT_POSNEG;
    } else {
      S.var_types[var] = output > 0 ? OUTPUT_POS : OUTPUT_NEG;
    }

    ++i;
  }

#ifdef POSQ_OUTPUTS
  for (int posqOutput: posqOutputs) S.var_types[var(all_outputs[posqOutput])] = OUTPUT_POSQ;
#endif

  for (int final_: finals) finals_set.insert(final_);

  while (nVars > S.nVars()) S.newVar();

  {
    vec<Lit>    lits;
    int i = 0;
    for (auto clause: clauses) {
      lits.clear();

      bool optional = false;
      if (clause.back() == 0) {
        optional = true;
        clause.pop_back();
      }

#ifdef OPTIONAL_CLAUSES
      if (!optional) {
#else
      {
#endif

#ifdef UPWARD_CLAUSES
        if (upwardClausesSet.contains(i)) {
          auto out0 = clause[0];
          int var = abs(out0) - 1;
          Lit out = out0 > 0 ? Lit(var) : Lit(var, true);
          for (int j = 1; j < clause.size(); ++j) {
            auto lit = clause[j];
            int var = abs(lit) - 1;
            lits.push(lit > 0 ? Lit(var) : Lit(var, true));
          }
          S.addUpwardClause(out, lits, upward_clauses_ww);
        } else {
#else
        {
#endif
          for (auto lit: clause) {
            int var = abs(lit) - 1;
            lits.push(lit > 0 ? Lit(var) : Lit(var, true));
          }
          S.addClause(lits, clauses_ww);
        }
        if (!S.okay())
          return false;
      }
      ++i;
    }
  }

  return S.okay();
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
  std::vector<Lit> all_outputs;
  vector<AfaHorline> horlines;
  vector<Head*> verlines;
  vector<Clause*> clauses_ww;
  vector<UpwardClause*> upward_clauses_ww;
  std::unordered_set<unsigned> finals;
  bool result = false;

  Solver S;
  int acnt;
  if (!parse_cnfafa(S, acnt, all_outputs, clauses_ww, upward_clauses_ww, finals)) return false;

  vector<int> order1;
  order1.reserve(S.nVars());
  vector<int> order2;
  order2.reserve(S.nVars());
  for (int i = 0; i < S.nVars(); ++i) {
    VarType vtype = S.var_types[i];
    if (vtype == OUTPUT_POS || vtype == OUTPUT_NEG || vtype == OUTPUT_POSNEG) {
      order1.push_back(i);
    } else if (vtype == GUESS_VAR) {
      order2.push_back(i);
    }
  }

#ifdef HEAP_VARORDER
  S.heap_order.init(order1);
#endif

#ifdef BUBBLE_VARORDER
  S.bubble_order.init(order1);
#endif

#ifdef WATCH_VARORDER
  S.watch_order.init(order1);
  S.finish_order.init();
#endif

#ifdef HEAP_VARORDER2
  S.heap_order2.init(order2);
#endif

#ifdef BUBBLE_VARORDER2
  S.bubble_order2.init(order2);
#endif

#ifdef WATCH_VARORDER2
  S.watch_order2.init(order2);
#endif

  if (finals.contains(0)) return true;
  vec<Lit> outputs;
  vec<Lit> inputs;

  for (unsigned i = 0; i < all_outputs.size(); ++i) {
    if (!finals.contains(i)) {
      outputs.push(all_outputs[i]);
      inputs.push(Lit(i, true));
    }
  }

#ifdef USE_TRIE
  AfaHorline &horline = horlines.emplace_back((Head*)NULL);
  Head &verhead = horline.elems.emplace_back(outputs[0]);

  unsigned depth = 0;
  S.trie.root = &verhead;

  Head *verline = verlines.emplace_back(new Head[outputs.size() - 1]);

  Head *above = &verhead;
  for (unsigned i = 1; i != outputs.size(); ++i) {
    Head &horhead = verline[i - 1];
    horhead.tag = outputs[i];
    horhead.above = above;

    if (i == 1) verhead.dual_next = &horhead;
    else above->next = &horhead;

    horhead.depth = ++depth;

    above = &horhead;
  }

  vector<unsigned> sharing_set;
  sharing_set.resize(S.watches.size(), 0);
#else
  if (verbosity >= 2) printf("FINAL_ANTICHAIN_CLAUSE\n");
  S.addClause(outputs, clauses_ww);
#endif

#ifdef WATCH_CLAUSE_WATCH
  for (Clause *clause: clauses_ww) {
    S.watch_on(clause->data[0]);
  }
  for (UpwardClause *clause: upward_clauses_ww) {
    S.watch_on(clause->output);
  }
#endif

  unsigned solveCnt = 0;
  unsigned satCnt = 0;
  unsigned unsatCnt = 0;

#ifdef CELL_CONTAINER_SET
  CellContainerSet cell_container;
#elif CELL_CONTAINER_DFS
  CellContainerDfs cell_container;
#elif CELL_CONTAINER_BFS
  CellContainerBfs cell_container;
#else
  ERROR
#endif

  while (true) {
    if (verbosity >= -3) printf("SOLVING %u\n", solveCnt);

#ifdef USE_TRIE
    if (verbosity >= 2) {
      S.trie.print_guards(S);
      if (write_debug_dots) {
        std::stringstream ss;
        ss << "debug/trie" << solveCnt << ".dot";
        string s;
        ss >> s;
        S.trie.to_dot(S, s.c_str());
      }
    }
#endif

    ++solveCnt;
    if (verbosity >= -4) {
      if (solveCnt % 1000 == 0) {
        std::cout << "MID " << solveCnt << " " << satCnt << " " << unsatCnt << std::endl;
      }
    }

    result = S.solve(inputs);
    if (result) while (true) {
      if (verbosity >= -3) printf("SOLVING_RESUME %d\n", solveCnt);

#ifdef USE_TRIE
      if (verbosity >= 2) {
        S.trie.print_guards(S);

        if (write_debug_dots) {
          std::stringstream ss;
          ss << "debug/trie" << solveCnt << ".dot";
          string s;
          ss >> s;
          S.trie.to_dot(S, s.c_str());
        }
      }
#endif

      ++solveCnt;
      if (verbosity >= -4) {
        if (solveCnt % 1000 == 0) {
          std::cout << "MID " << solveCnt << " " << satCnt << " " << unsatCnt << std::endl;
        }
      }

      result = S.resume();
      if (!result) break;
      ++satCnt;

      outputs.clear();
      inputs.clear();

      for (int i = 0; i < all_outputs.size(); ++i) {
        Lit out = all_outputs[i];

        if (S.value(out) == l_False) {
          outputs.push(out);
          inputs.push(Lit(i, true));
        }
        else if (i == 0) goto finally;
      }

      cell_container.add(inputs);

#ifdef USE_TRIE
      S.trie.onSat(S, S.nConstrs++, sharing_set, outputs, horlines, verlines);
#else
      {
        Clause *c;
        Clause_new_handleConflict(S, outputs, c);
        if (verbosity >= 2) {
          printf("RECORD_ANTICHAIN %p %p", c, c ? c->getSpecificPtr2() : c);
          for (int j = 0; j < outputs.size(); ++j) {
            std::cout << " " << outputs[j];
          }
          std::cout << std::endl;
        }
        S.constrs.push(c);
        ++S.nConstrs;

        int max_level = -1;
        const Lit* end = &outputs[outputs.size()];
        for (Lit *xptr = outputs; xptr != end; ++xptr) {
          Lit x = *xptr;
          int lvl = S.level[var(x)];
          if (lvl > max_level) {
            max_level = lvl;
          }
        }
        S.cancelUntil(max_level);
      }
#endif
      {
        Lit *end = &outputs[outputs.size()];
        for (Lit *out = &outputs[0]; out != end; ++out) {
          *out = ~*out;
        }
      }

      if (!S.onSatConflict(std::move(outputs))) {
        if (verbosity >= 2) printf("STOP\n");
        result = false;
        break;
      }
      if (verbosity >= 2) printf("NEXT\n");
    }

    // TODO nLearnts

    ++unsatCnt;

    if (!cell_container.size()) break;
    inputs = std::move(cell_container.pop());

    S.reset();
  }

finally:
  for (Head *verline: verlines) delete[] verline;
  return result;
}

int main(int argc, char** argv) {
    srand(1345719);
    char mode = '3';
    if (argc >= 2) mode = argv[1][0];

    if (run()) {
        std::cout << "NOT_EMPTY" << std::endl;
    } else {
        std::cout << "EMPTY" << std::endl;
    }
}
