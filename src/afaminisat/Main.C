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

using std::cout;
using std::endl;
using std::vector;
using std::string;
namespace chrono = std::chrono;

#ifdef MY_DEBUG
int verbosity = 4;
const int VERBOSE_FROM = -1;
#endif
const bool write_debug_dots = false;
int port = 4002;

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

bool parse_cnfafa(Solver& S, int* acnt) {
  *acnt = getIntLine().second[0];
  std::vector<int> outputs(std::move(getIntLine().second));
  std::vector<int> finals(std::move(getIntLine().second));
  std::vector<int> pureVars(std::move(getIntLine().second));
  std::vector<int> upwardClauses(std::move(getIntLine().second));
  std::vector<int> posqOutputs(std::move(getIntLine().second));

  int nVars = *acnt + outputs.size();

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

  S.pures.growTo(nVars, false);

  for (int pure: pureVars) S.pures[pure] = true;
  for (unsigned i = 0; i < outputs.size(); ++i) S.pures[i] = true;

  unordered_set<unsigned> upwardClausesSet;
  for (auto upward: upwardClauses) upwardClausesSet.insert(upward);

  S.trie.posq_output_map.resize(nVars, false);

  int i = 0;
  for (int output: outputs) {
    int var = abs(output) - 1;
    Lit lit = output > 0 ? Lit(var) : Lit(var, true);
    S.outputs.push(lit);
    ++i;
  }

  for (int posqOutput: posqOutputs) {
    S.trie.posq_output_map[var(S.outputs[posqOutput])] = true;
  }

  for (auto final_: finals) S.finals.insert(final_);

  while (nVars > S.nVars()) S.newVar();

  {
    vec<Lit>    lits;
    int i = 0;
    for (auto clause: clauses) {
      lits.clear();
      if (upwardClausesSet.contains(i)) {
        auto out0 = clause[0];
        int var = abs(out0) - 1;
        Lit out = out0 > 0 ? Lit(var) : Lit(var, true);
        for (int j = 1; j < clause.size(); ++j) {
          auto lit = clause[j];
          int var = abs(lit) - 1;
          lits.push(lit > 0 ? Lit(var) : Lit(var, true));
        }
        S.addUpwardClause(out, lits);
      } else {
        for (auto lit: clause) {
          int var = abs(lit) - 1;
          lits.push(lit > 0 ? Lit(var) : Lit(var, true));
        }
        S.addClause(lits);
      }
      if (!S.okay())
        return false;
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

bool extract_sat_result(
    Solver &S,
    vector<int> &cell,
    // only for logging purposes:
    const CellContainer &cell_container,
    int acnt, int satCnt, int unsatCnt, int &maxDepth, int omitted
) {
    if (verbosity >= -1)
        printf("***********************************************\nq ");
    for (int i = 0; i < S.outputs.size(); i++) {
        Lit out = S.outputs[i];

        if (S.value(out) == l_False) // WARNING solver must not be reset after sat
        {
            if (verbosity >= -1) printf("0");
            cell.push_back(i);
        }
        else if (i == 0) return true;
        else if (verbosity >= -1)
            printf("%c", S.value(out) == l_Undef ? 'x' : '1');
    }

    if (verbosity >= -1) {
        printf("\n");
        printf("\na ");
        for (int i = S.outputs.size(); i < S.outputs.size() + acnt; i++) {
            printf(
                "%c",
                S.value(i) == l_True
                    ? '1'
                    : (S.value(i) == l_False ? '0' : 'x')
            );
        }
        printf("\n\n");
        cout << satCnt << " " << unsatCnt << " " << omitted
          << " " << cell_container.size() << endl;
        printf("-----------------------------------------------\n\n");
    }
    maxDepth = max(cell_container.size(), maxDepth);

    return false;
}


class ModelCheckingImpl final {
    Solver S;
    int acnt;
    CellContainerSet cell_container;
    vector<int> *cell;
    vec<Lit> cell_out;
    vec<Lit> solver_input;
    MeasuredSupQ container_supq;

public:
    int solveCnt = 0;
    int satCnt = 0;
    int unsatCnt = 0;
    int maxDepth = 0;
    int omitted = 0;
    int reset_count = 0;
    bool short_unsat = false;
    bool short_sat = false;

    ModelCheckingImpl(char mode) : container_supq()
    {
        switch (mode) {
          case '0': TRIE_MODE = clauses; break;
          default: TRIE_MODE = branch_always;
        }

        short_unsat = !parse_cnfafa(S, &acnt);
        if (short_unsat) {
            return;
        }
        solver_input.growTo(S.outputs.size());

        cell = new vector<int>(S.outputs.size() - S.finals.size());
        int j = 0;
        for (int i = 0; i < S.outputs.size(); i++) {
          if (!S.finals.contains(i)) {
            (*cell)[j++] = i;
          }
        }
        if (verbosity >= 2) {printf("ncell1"); for(int i: *cell){printf(" %d", i);} printf("\n");}

        vec<Lit> unique_outputs;
        std::unordered_set<int> unique_outputs_set;
        for (int i = 0; i < S.outputs.size(); i++) {
          if (!unique_outputs_set.contains(index(S.outputs[i]))) {
            unique_outputs_set.insert(index(S.outputs[i]));
            unique_outputs.push(S.outputs[i]);
          }
        }
        if (TRIE_MODE == clauses) {
          S.trie.init_clausal(unique_outputs, S);
        } else {
          short_sat = !S.trie.init(unique_outputs, S.finals, S);
          if (short_sat) return;
        }
        S.order.init();

        if (verbosity >= 2) {
            for (int x = 0; x < S.outputs.size(); x++) {
                printf("VAR %d " L_LIT "\n", x, L_lit(S.outputs[x]));
            }
        }
    }

    bool modelCheck() {
        if (short_unsat) {
            return false;
        }
        if (short_sat) {
            return true;
        }

        S.status = Solver_RUNNING;
        S.tic = chrono::steady_clock::now();

        bool st;
        bool empty;

        while (true) {
            if (false) { // (container_supq.get_or_add(*cell)) {
              delete cell;
              omitted++;
            } else {
              solver_input.clear();
              for(int i: *cell) {
                solver_input.push(Lit(i, true));
              }

              if (verbosity >= -1) {
                printf("==================\ni ");
                unsigned j = 0;
                for (int i = 0; i < S.outputs.size(); i++) {
                  if (j < cell->size() && (*cell)[j] == i) {
                    printf("0");
                    j++;
                  }
                  else {
                    printf("x");
                  }
                }
                printf("\n==================\n");
              }

#ifdef MY_DEBUG
              if (solveCnt == VERBOSE_FROM) verbosity = 3;
#endif
              if (verbosity >= -3) printf("SOLVING %d\n", solveCnt);
              if (verbosity >= 2) {
                S.trie.print_places();
                if (write_debug_dots) {
                  std::stringstream ss;
                  ss << "debug/trie" << solveCnt << ".dot";
                  string s;
                  ss >> s;
                  S.trie.to_dot(S, s.c_str());
                }
              }
              solveCnt++;
              if (verbosity >= -4) {
                if (solveCnt % 1000 == 0) {
                  std::cout << "MID " << solveCnt << " " << satCnt << " " << unsatCnt << " " << global_bubble_move_count << " " << global_bubble_move_count_undo << std::endl;
                }
              }
              st = S.solve(solver_input);

              delete cell;

              if (st) {
                  while (true) {
#ifdef MY_DEBUG
                      if (solveCnt == VERBOSE_FROM) verbosity = 3;
#endif
                      if (verbosity >= -3) printf("SOLVING_RESUME %d\n", solveCnt);
                      if (verbosity >= 2) {
                        S.trie.print_places();

                        if (write_debug_dots) {
                          std::stringstream ss;
                          ss << "debug/trie" << solveCnt << ".dot";
                          string s;
                          ss >> s;
                          S.trie.to_dot(S, s.c_str());
                        }
                      }
                      solveCnt++;
                      if (verbosity >= -4) {
                        if (solveCnt % 1000 == 0) {
                          std::cout << "MID " << solveCnt << " " << satCnt << " " << unsatCnt << " " << global_bubble_move_count << " " << global_bubble_move_count_undo << std::endl;
                        }
                      }

                      if (!S.resume()) break;
                      satCnt++;

                      cell = new vector<int>();

                      if (extract_sat_result(
                              S, *cell,
                              cell_container, acnt, satCnt,
                              unsatCnt, maxDepth, omitted
                      )) {
                          delete cell;
                          empty = false;
                          goto finally;
                      }
                      if (verbosity >= 2) {printf("ncell2"); for(int i: *cell){printf(" %d", i);} printf("\n");}

                      cell_container.add(cell);

                      if (TRIE_MODE == clauses) {
                          cell_out.clear();
                          for (int i: *cell) {
                              cell_out.push(S.outputs[i]);
                          }

                          Clause *c;
                          bool ok_ = Clause_new_handleConflict(S, cell_out, c);
                          if (verbosity >= 2) {
                            printf("RECORD_ANTICHAIN %p %p", c, c ? c->getSpecificPtr2() : c);
                            for (int j = 0; j < cell_out.size(); ++j) {
                              std::cout << " " << cell_out[j];
                            }
                            std::cout << std::endl;
                          }
                          assert(!ok_);
                          if (c == NULL) break;
                          S.addConstr(c);
                      } else {
                          S.trie.onSat(S);
                      }

                      if (!S.onSatConflict(*cell)) {
                        if (verbosity >= 2) printf("STOP\n");
                        break;
                      }
                      if (verbosity >= 2) printf("NEXT\n");
                  };
              }
            }

            unsatCnt++;

            if (!cell_container.size()) break;
            cell = cell_container.pop();
            if (verbosity >= 2) {printf("pcell"); for(int i: *cell){printf(" %d", i);} printf("\n");}

            S.reset();

            if (verbosity >= -2) {
              reset_count++;
              printf("memstats %u %d %d %d %d\n", reset_count, hor_head_count, hor_count, ver_count, S.nLearnts());
            }
        }

        empty = true;

    finally:
        // printStats(S.stats, cpuTime());
        if (verbosity >= 2) {
            cout
            << satCnt << " "
            << unsatCnt << " "
            << maxDepth << " "
            << omitted << " "
            << container_supq.elapsed_add.count() << " "
            << container_supq.elapsed_get.count() << " "
            << endl;
        }

        return empty;
    }
};

int main(int argc, char** argv) {
    srand(1345719);
    char mode = '3';
    if (argc >= 2) mode = argv[1][0];

    {
      ModelCheckingImpl mc(mode);
      if (mc.modelCheck()) {
          std::cout << "EMPTY " << mc.solveCnt << " " << mc.satCnt << " " << mc.unsatCnt << " " << global_bubble_move_count << " " << global_bubble_move_count_undo << std::endl;
      } else {
          std::cout << "NOT_EMPTY " << mc.solveCnt << " " << mc.satCnt << " " << mc.unsatCnt << " " << global_bubble_move_count << " " << global_bubble_move_count_undo << std::endl;
      }
      if (verbosity >= -2) printf("memstats %d %d %d\n", hor_head_count, hor_count, ver_count);
    }
    if (verbosity >= -2) printf("memstats %d %d %d\n", hor_head_count, hor_count, ver_count);
}
