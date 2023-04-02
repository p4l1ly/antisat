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
#include <automata-safa-capnp/Afa/Model/CnfAfa.capnp.h>
#include <automata-safa-capnp/Afa/Rpc/ModelChecker.capnp.h>
#include <automata-safa-capnp/Afa/Rpc/ModelCheckers.capnp.h>

#include <ctime>
#include <unistd.h>
#include <signal.h>
#include <chrono>
#include <iostream>
#include <vector>
#include <string>
#include <algorithm>

#include <capnp/ez-rpc.h>
#include <kj/thread.h>

using std::cout;
using std::endl;
using std::vector;
using std::string;
namespace chrono = std::chrono;

namespace cnfafa = automata_safa_capnp::model::cnf_afa;
namespace mc = automata_safa_capnp::rpc::model_checker;
namespace mcs = automata_safa_capnp::rpc::model_checkers;

bool use_trie = true;
int port = 4002;

bool parse_cnfafa(const cnfafa::Afa::Reader &in, Solver& S, int* acnt) {
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
          << " " << cell_container.size() << endl;
        printf("-----------------------------------------------\n\n");
    }
    maxDepth = max(cell_container.size(), maxDepth);

    return false;
}

class ControlImpl final: public mc::Control::Server {
    Solver* S;

public:
    ControlImpl(Solver* S_) : S(S_) {}

    kj::Promise<void> pause(PauseContext context) override {
        setStatus(context.getResults().getOldStatus());
        if (S->status == Solver_RUNNING) {
            S->pauseMutex.lock();
            S->status = Solver_PAUSED;
            S->runningMutex.lock();
            S->pauseMutex.unlock();
        };
        return kj::READY_NOW;
    }

    kj::Promise<void> resume(ResumeContext context) override {
        setStatus(context.getResults().getOldStatus());
        if (S->status == Solver_PAUSED) {
            S->status = Solver_RUNNING;
            S->runningMutex.unlock();
        }
        return kj::READY_NOW;
    }

    kj::Promise<void> cancel(CancelContext context) override {
        setStatus(context.getResults().getOldStatus());
        int old_status = S->status;
        S->status = Solver_CANCELLED;
        if (old_status == Solver_PAUSED) {
            S->runningMutex.unlock();
        }
        return kj::READY_NOW;
    }

    kj::Promise<void> getStatus(GetStatusContext context) override {
        setStatus(context.getResults().getStatus());
        return kj::READY_NOW;
    }

private:
    void setStatus(mc::Status::Builder status) {
        std::chrono::duration<double> t;
        if (S->status == Solver_PAUSED) t = S->elapsed;
        else t = S->elapsed + chrono::steady_clock::now() - S->tic;

        status.setTime(t.count()*1000);

        switch(S->status) {
            case Solver_RUNNING:
                status.setState(mc::State::RUNNING);
                return;
            case Solver_INIT:
                status.setState(mc::State::INIT);
                return;
            case Solver_CANCELLED:
                status.setState(mc::State::CANCELLED);
                return;
            case Solver_PAUSED:
                status.setState(mc::State::PAUSED);
                return;
        }
    }
};

class ModelCheckingImpl final: public mc::ModelChecking<mcs::Emptiness>::Server {
    Solver S;
    int acnt;
    CellContainerSet cell_container;
    vector<int> *cell;
    vec<Lit> cell_out;
    Trie *trie;
    vec<Lit> solver_input;
    MeasuredSupQ container_supq;

    int satCnt = 0;
    int unsatCnt = 0;
    int maxDepth = 0;
    int omitted = 0;
    int reset_count = 0;
    bool short_unsat = false;

public:
    ModelCheckingImpl(cnfafa::Afa::Reader cnfafa)
    : solver_input(cnfafa.getOutputs().size())
    , container_supq()
    {
        short_unsat = !parse_cnfafa(cnfafa, S, &acnt);
        if (short_unsat) {
            return;
        }

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
        auto result = context.getResults();

        if (short_unsat) {
            result.getMeta().setEmpty(true);
            result.setTime(0);
            return kj::READY_NOW;
        }

        kj::MutexGuarded<kj::Maybe<const kj::Executor&>> executor;
        kj::Own<kj::PromiseFulfiller<void>> fulfiller;

        kj::Thread([&]() noexcept {
            kj::EventLoop loop;
            kj::WaitScope scope(loop);

            auto paf = kj::newPromiseAndFulfiller<void>();
            fulfiller = kj::mv(paf.fulfiller);

            *executor.lockExclusive() = kj::getCurrentThreadExecutor();
            paf.promise.wait(scope);
        }).detach();

        const kj::Executor *exec;
        {
            auto lock = executor.lockExclusive();
            lock.wait([&](kj::Maybe<const kj::Executor&> value) {
                return value != nullptr;
            });
            exec = &KJ_ASSERT_NONNULL(*lock);
        }

        return exec->executeAsync(
            [this, result, fulfiller{kj::mv(fulfiller)}]() mutable {
                try {
                    result.getMeta().setEmpty(modelCheck());
                }
                catch(Cancelled c) {
                    result.setCancelled(true);
                }

                std::chrono::duration<double> t;
                t = S.elapsed + chrono::steady_clock::now() - S.tic;
                result.setTime(t.count()*1000);

                fulfiller->fulfill();
            }
        );
    }

    kj::Promise<void> getControl(GetControlContext context) override {
        context.getResults().setControl(kj::heap<ControlImpl>(&S));
        return kj::READY_NOW;
    }

private:
    bool modelCheck() {
        if (short_unsat) {
            return false;
        }

        S.status = Solver_RUNNING;
        S.tic = chrono::steady_clock::now();

        bool st;
        bool empty;

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

              st = S.solve(solver_input);

              if (verbosity >= 2) {printf("dcell1"); for(int i: *cell){printf(" %d", i);} printf("\n");}
              delete cell;

              if (st) {
                  while (S.resume()) {
                      satCnt++;

                      cell = new vector<int>();

                      if (extract_sat_result(
                              S, *cell,
                              cell_container, acnt, satCnt,
                              unsatCnt, maxDepth, omitted
                      )) {
                          if (verbosity >= 2) {printf("ncell2"); for(int i: *cell){printf(" %d", i);} printf("\n");}
                          if (verbosity >= 2) {printf("dcell2"); for(int i: *cell){printf(" %d", i);} printf("\n");}
                          delete cell;
                          empty = false;
                          goto finally;
                      }
                      if (verbosity >= 2) {printf("ncell2"); for(int i: *cell){printf(" %d", i);} printf("\n");}

                      cell_container.add(cell);

                      Place cut_knee = {NULL, 0, 0};

                      if (use_trie) {
                          if (trie->onSat(S)) cut_knee = *trie;
                      } else {
                          cell_out.clear();
                          for (int i: *cell) {
                              cell_out.push(S.outputs[i]);
                          }

                          Clause *c;
                          bool ok_ = Clause_new_handleConflict(S, cell_out, c);
                          assert(!ok_);
                          if (c == NULL) break;
                          S.addConstr(c);
                      }

                      if (!S.onSatConflict(*cell)) {
                        if (verbosity >= 2) printf("STOP %d\n", cut_knee.hor != NULL);
                        if (cut_knee.hor) cut_knee.cut_away();
                        break;
                      }
                      if (verbosity >= 2) printf("NEXT\n");
                      if (cut_knee.hor) cut_knee.cut_away();
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
              if (reset_count % 10000 == 0) {
                printf("memstats %u %d %d %d %d\n", reset_count, hor_head_count, hor_count, ver_count, S.nLearnts());
              }
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

class ModelCheckerImpl final: public mc::ModelChecker<cnfafa::Afa, mcs::Emptiness>::Server {
public:
    kj::Promise<void> load(LoadContext context) override {
        cnfafa::Afa::Reader cnfafa = context.getParams().getModel();
        context.getResults().setChecking(kj::heap<ModelCheckingImpl>(cnfafa));
        return kj::READY_NOW;
    }
};

int main(int argc, char** argv) {
    if (argc >= 2 && argv[1][0] == '0') use_trie = false;
    if (argc >= 3) port = atoi(argv[2]);

    capnp::EzRpcServer server(kj::heap<ModelCheckerImpl>(), "0.0.0.0", port);
    auto& waitScope = server.getWaitScope();
    kj::NEVER_DONE.wait(waitScope);
}
