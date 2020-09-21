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
#include <automata-safa-capnp/CnfAfa.capnp.h>
#include <automata-safa-capnp/CnfAfaRpc.capnp.h>

#include <ctime>
#include <unistd.h>
#include <signal.h>
#include <chrono>
#include <iostream>
#include <vector>
#include <string>
#include <algorithm>

#include <capnp/message.h>
#include <capnp/serialize-packed.h>
#include <capnp/ez-rpc.h>

using std::cout;
using std::endl;
using std::vector;
using std::string;
namespace chrono = std::chrono;

namespace schema = automata_safa_capnp::cnf_afa;
namespace rpcschema = automata_safa_capnp::cnf_afa_rpc;

bool parse_cnfafa(const schema::CnfAfa::Reader &in, Solver& S, int* acnt) {
    *acnt = in.getVariableCount();
    auto outputs = in.getOutputs();
    auto clauses = in.getClauses();

    int nVars = *acnt + outputs.size() + clauses.size();
    S.pures.growTo(nVars, false);
    S.output_map.growTo(nVars, -1);

    int i = 0;
    for (auto output: outputs) {
        int var = output.getVar();
        S.output_map[var] = i;
        Lit lit = output.getPositive() ? Lit(var) : Lit(var, true);
        S.outputs.push(lit);
        S.impure_outputs.push(lit);
        i++;
    }

    while (nVars > S.nVars()) S.newVar();

    vec<Lit>    lits;
    for (auto clause: clauses) {
        lits.clear();
        for (auto lit: clause) {
            int var = lit.getVar();
            lits.push(lit.getPositive() ? Lit(var) : Lit(var, true));
        }
        S.addClause(lits);
        if (!S.okay())
            return false;
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
    chrono::duration<double> &elapsed_sat,
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
                S.model[i] == l_True
                    ? '1'
                    : (S.model[i] == l_False ? '0' : 'x')
            );
        }
        printf("\n\n");
        cout << satCnt << " " << unsatCnt << " " << omitted
          << " " << cell_container.size() << " " << elapsed_sat.count() << endl;
        printf("-----------------------------------------------\n\n");
    }
    maxDepth = max(cell_container.size(), maxDepth);

    return false;
}

class LoadedModelImpl final: public rpcschema::LoadedModel::Server {
    GlobSolver GS;
    Solver S;
    int acnt;
    CellContainerSet cell_container;
    vector<int> *cell;
    Trie *trie;
    vec<Lit> solver_input;
    MeasuredSupQ container_supq;

    chrono::duration<double> elapsed_sat;
    chrono::time_point<chrono::steady_clock> tic_all;
    chrono::time_point<chrono::steady_clock> tic;
    int satCnt = 0;
    int unsatCnt = 0;
    int maxDepth = 0;
    int omitted = 0;
    int reset_count = 0;

public:
    LoadedModelImpl(schema::CnfAfa::Reader cnfafa)
    : GS()
    , S(GS)
    , cell_container()
    , elapsed_sat(chrono::duration<double>::zero())
    , solver_input(cnfafa.getOutputs().size())
    , container_supq()
    {
        parse_cnfafa(cnfafa, S, &acnt);

        cell = new vector<int>(S.outputs.size());
        for (int i = 0; i < S.outputs.size(); i++) (*cell)[i] = i;
        if (verbosity >= 2) {printf("ncell1"); for(int i: *cell){printf(" %d", i);} printf("\n");}


        trie = new Trie(S.outputs.size(), S.nVars() * 2);
        S.trie = trie;
        S.addConstr(trie);

        if (verbosity >= 2) {
            for (int x = 0; x < S.outputs.size(); x++) {
                printf("VAR %d " L_LIT "\n", x, L_lit(S.outputs[x]));
            }
        }
    }

    kj::Promise<void> solve(SolveContext context) override {
        context.getResults().setEmpty(modelCheck());
        return kj::READY_NOW;
    }

private:
    bool modelCheck() {
        bool st;
        bool is_empty;

        tic_all = chrono::steady_clock::now();
        tic = chrono::steady_clock::now();

        while (true) {
            if (false) { // (container_supq.get_or_add(*cell)) {
              if (verbosity >= 2) {printf("dcell0"); for(int i: *cell){printf(" %d", i);} printf("\n");}
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

              tic = chrono::steady_clock::now();
              st = S.solve(solver_input);
              elapsed_sat = elapsed_sat + chrono::steady_clock::now() - tic;

              if (verbosity >= 2) {printf("dcell1"); for(int i: *cell){printf(" %d", i);} printf("\n");}
              delete cell;

              if (st) {
                  tic = chrono::steady_clock::now();
                  while (S.resume()) {
                      elapsed_sat = elapsed_sat + chrono::steady_clock::now() - tic;
                      satCnt++;

                      cell = new vector<int>();

                      if (extract_sat_result(
                              S, *cell, elapsed_sat,
                              cell_container, acnt, satCnt, unsatCnt, maxDepth,
                              omitted)) {
                          if (verbosity >= 2) {printf("ncell2"); for(int i: *cell){printf(" %d", i);} printf("\n");}
                          if (verbosity >= 2) {printf("dcell2"); for(int i: *cell){printf(" %d", i);} printf("\n");}
                          delete cell;
                          is_empty = false;
                          goto finally;
                      }
                      if (verbosity >= 2) {printf("ncell2"); for(int i: *cell){printf(" %d", i);} printf("\n");}

                      cell_container.add(cell);

                      tic = chrono::steady_clock::now();
                      CutKnee cut_knee = trie->onSat(S);
                      if (!S.onSatConflict(*cell)) {
                        if (verbosity >= 2) printf("STOP %d\n", cut_knee.enabled);
                        if (cut_knee.enabled) cut_knee.knee.cut();
                        break;
                      }
                      if (verbosity >= 2) printf("NEXT\n");
                      if (cut_knee.enabled) cut_knee.knee.cut();
                  };
                  elapsed_sat = elapsed_sat + chrono::steady_clock::now() - tic;
              }
            }

            unsatCnt++;

            if (!cell_container.size()) break;
            cell = cell_container.pop();
            if (verbosity >= 2) {printf("pcell"); for(int i: *cell){printf(" %d", i);} printf("\n");}

            tic = chrono::steady_clock::now();
            S.reset();
            elapsed_sat = elapsed_sat + chrono::steady_clock::now() - tic;

            if (verbosity >= -2) {
              reset_count++;
              if (reset_count % 10000 == 0) {
                printf("memstats %u %d %d %d %d\n", reset_count, hor_head_count, hor_count, ver_count, S.nLearnts());
              }
            }
        }

        is_empty = true;

    finally:
        // printStats(S.stats, cpuTime());
        chrono::duration<double> elapsed_all = chrono::steady_clock::now() - tic_all;
        if (verbosity >= 2) {
            cout
            << satCnt << " "
            << unsatCnt << " "
            << maxDepth << " "
            << omitted << " "
            << elapsed_sat.count() << " "
            << elapsed_all.count() << " "
            << container_supq.elapsed_add.count() << " "
            << container_supq.elapsed_get.count() << " "
            << endl;
        }

        return is_empty;
    }
};

class LoaderImpl final: public rpcschema::Loader::Server {
public:
    kj::Promise<void> load(LoadContext context) override {
        schema::CnfAfa::Reader cnfafa = context.getParams().getModel();
        context.getResults().setLoadedModel(kj::heap<LoadedModelImpl>(cnfafa));
        return kj::READY_NOW;
    }
};

int main() {
    capnp::EzRpcServer server(kj::heap<LoaderImpl>(), "0.0.0.0", 4000);
    auto& waitScope = server.getWaitScope();
    kj::NEVER_DONE.wait(waitScope);
}
