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

#include "Solver.h"
#include "Sort.h"
#include "Trie.h"
#include <cmath>
#include <iostream>
#include <cstdlib>


//=================================================================================================
// Debug:


// Just like 'assert()' but expression will be evaluated in the release version as well.
inline void check(bool expr) { assert(expr); }

//=================================================================================================
// Minor methods:


Solver::~Solver(void) {
    for (int i = 0; i < learnts.size(); i++) xfree(learnts[i]);
    for (int i = 0; i < constrs.size(); i++) xfree(constrs[i]);
}

// Creates a new SAT variable in the solver. If 'decision_var' is cleared, variable will not be
// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
//
Var Solver::newVar(bool pure)
{
    int     index;
    index = nVars();
    watches  .push();          // (list for positive literal)
    watches  .push();          // (list for negative literal)
    reason   .push(NULL);
    assigns  .push(toInt(l_Undef));
    level    .push(-1);
    activity .push(0);
    order    .newVar();
    return index;
}


// Returns FALSE if immediate conflict.
bool Solver::assume(Lit p) {
    assert(propQ.size() == 0);
    if (verbosity >= 2) {
        printf(L_LIT "\n", L_lit(p));
    }
    if (verbosity >= 2) printf(L_IND "assume(" L_LIT ", %d, %ld)\n", L_ind, L_lit(p), trail.size(), undos.size());
    trail_lim.push(std::pair(trail.size(), undos.size()));
    return enqueue(p); }


inline void Solver::undoOneLevel() {
    auto start_u = undos.begin() + trail_lim.last().second;
    auto stop_u = undos.end();
    if (verbosity >= 2) printf(L_IND "undoOneLevel(%d, %ld)\n", L_ind, trail_lim.last().second, undos.size());
    for (auto u = start_u; u != stop_u; ++u) (*u)->undo(*this);
    undos.erase(start_u, stop_u);
    trail_lim.pop();
}


// Reverts to the state before last 'assume()'.
//
void Solver::cancel(void)
{
    assert(propQ.size() == 0);
    int stop = trail_lim.last().first;
    if (verbosity >= 2){
      if (trail.size() != stop){
        Lit p = trail[stop]; printf(L_IND "cancel(" L_LIT ")\n", L_ind, L_lit(p));
      }
    }
    for (int c = trail.size() - stop; c; c--) undoOne();
    undoOneLevel();
}


// Revert to the state at given level.
//
void Solver::cancelUntil(int level) {
    while (decisionLevel() > level) cancel();
}


// Record a clause and drive backtracking. 'clause[0]' must contain the asserting literal.
//
void Solver::record(const vec<Lit>& clause)
{
    assert(clause.size() != 0);
    Clause* c;
    check(Clause_new(*this, clause, true, c));
    check(ok);
    check(enqueue(clause[0], c));
    if (c != NULL) learnts.push(c);
}


//=================================================================================================
// Major methods:

bool Solver::onSatConflict(const vector<int>& cell) {
  stats.conflicts++;

  if (verbosity >= 2) {
      printf(L_IND "**CONFLICT2**", L_ind);
      printf("{");
      for(int x: cell) printf(" %d", x);
      printf(" }\n");
  }

  vec<Lit>    learnt_clause;
  int         backtrack_level;

  if (decisionLevel() <= root_level) {
      if (verbosity >= 2) printf("DECLEVEL\n");
      return false;
  }

  if (!analyze2(cell, learnt_clause, backtrack_level)) {
      if (verbosity >= 2) printf("DECLEVEL2\n");
      return false;
  }

  cancelUntil(max(backtrack_level, root_level));
  record(learnt_clause);
  varDecayActivity(); claDecayActivity();

  return true;
}


/*_________________________________________________________________________________________________
|
|  analyze : (confl : Constr*) (out_learnt : vec<Lit>&) (out_btlevel : int&)  ->  [void]
|  
|  Description:
|    Analyze conflict and produce a reason clause.
|  
|    Pre-conditions:
|      * 'out_learnt' is assumed to be cleared.
|      * Current decision level must be greater than root level.
|  
|    Post-conditions:
|      * 'out_learnt[0]' is the asserting literal at level 'out_btlevel'.
|  
|  Effect:
|    Will undo part of the trail, upto but not beyond the assumption of the current decision level.
|________________________________________________________________________________________________@*/
bool Solver::analyze(Reason* confl, vec<Lit>& out_learnt, int& out_btlevel)
{
    vec<char>&  seen = analyze_seen;
    int         pathC    = 0;
    Lit         p = lit_Undef;
    vec<Lit>    p_reason;
    seen.growTo(nVars(), 0);
    int out_learnt_final_size;
    int out_btlevel_final;

    // Generate conflict clause:
    //
    out_learnt.push(lit_Undef);      // (leave room for the asserting literal)
    out_btlevel = 0;

    p_reason.clear();
    confl->calcReason(*this, p, p_reason);
    if (decisionLevel() <= root_level) return false;

    while (true) {
        if (verbosity >= 2) {
          printf("REASON " L_LIT ":", L_lit(p));
          for (int i = 0; i < p_reason.size(); i++) {
            printf(" " L_LIT, L_lit(p_reason[i]));
          }
          printf("\n");
        }

        for (int j = 0; j < p_reason.size(); j++){
            Lit q = p_reason[j];
            if (!seen[var(q)] && level[var(q)] > 0){
                seen[var(q)] = 1;
                varBumpActivity(q);
                if (level[var(q)] == decisionLevel())
                    pathC++;
                else{
                    if (verbosity >= 2) printf("PUSH " L_LIT " %d %d\n", L_lit(~q), level[var(q)], decisionLevel());
                    out_learnt.push(~q),
                    out_btlevel = max(out_btlevel, level[var(q)]);
                }
            }
        }

        // Select next clause to look at:
        while (true) {
            p = trail.last();
            confl = reason[var(p)];

            if (seen[var(p)]) {
              seen[var(p)] = 0;

              if (confl == NULL) {
                if (out_learnt[0] == lit_Undef) {
                  if (verbosity >= 2) printf("ASSERTING " L_LIT " %d\n", L_lit(~p), out_learnt.size());
                  out_learnt[0] = ~p;
                  out_learnt_final_size = out_learnt.size();
                  out_btlevel_final = out_btlevel;
                }
                undoOne(); if (trail_lim.last().first == trail.size()) undoOneLevel();
                goto resolved;
              }

              pathC--;

              if (pathC == 0 && out_learnt[0] == lit_Undef) {
                if (verbosity >= 2) printf("ASSERTING " L_LIT "\n", L_lit(~p));
                out_learnt[0] = ~p;
                out_learnt_final_size = out_learnt.size();
                out_btlevel_final = out_btlevel;
              }

              p_reason.clear();
              confl->calcReason(*this, p, p_reason);
              undoOne(); if (trail_lim.last().first == trail.size()) undoOneLevel();

              break;
            }

            undoOne(); if (trail_lim.last().first == trail.size()) undoOneLevel();

            if (confl == NULL) {
              if (verbosity >= 2) printf("OLD_LEVEL\n");
              pathC = 0;
              int max_level = out_btlevel;
              out_btlevel = 0;

              if (max_level <= root_level) {
                for (int j = 1; j < out_learnt.size(); j++) seen[var(out_learnt[j])] = 0;
                return false;
              }

              for (int j = 1; j < out_learnt.size(); j++) {
                Lit lit = out_learnt[j];
                int lvl = level[var(lit)];
                if (lvl == max_level) {
                  pathC++;
                }
                else {
                  out_btlevel = max(out_btlevel, lvl);
                  if (pathC) out_learnt[j - pathC] = lit;
                }
              }

              out_learnt.shrink(pathC);
              out_learnt[0] = lit_Undef;
              cancelUntil(max_level);
            }
        }
    }

resolved:

    for (int j = 0; j < out_learnt.size(); j++) seen[var(out_learnt[j])] = 0;    // ('seen[]' is now cleared)

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wmaybe-uninitialized"
    out_learnt.shrink(out_learnt.size() - out_learnt_final_size);
    out_btlevel = out_btlevel_final;
#pragma GCC diagnostic pop

    if (verbosity >= 2){
        printf(L_IND "Learnt ", L_ind);
        printClause(out_learnt);
        printf(" at level %d\n", out_btlevel);
    }

    return true;
}

bool Solver::analyze2(const vector<int>& cell, vec<Lit>& out_learnt, int& out_btlevel)
{
    vec<char>&  seen = analyze_seen;
    int         pathC    = 0;
    Lit         p = lit_Undef;
    vec<Lit>    p_reason;
    int out_learnt_final_size;
    int out_btlevel_final;

    seen.growTo(nVars(), 0);

    for (int i: cell) {
        p_reason.push(~outputs[i]);
    }

    // Generate conflict clause:
    //
    out_learnt.push(lit_Undef);      // (leave room for the asserting literal)
    out_btlevel = 0;
    while(true){
        for (int j = 0; j < p_reason.size(); j++){
            Lit q = p_reason[j];
            if (!seen[var(q)] && level[var(q)] > 0){
                seen[var(q)] = 1;
                varBumpActivity(q);
                if (level[var(q)] == decisionLevel())
                    pathC++;
                else{
                    out_learnt.push(~q),
                    out_btlevel = max(out_btlevel, level[var(q)]);
                }
            }
        }

        Reason* confl;

        // Select next clause to look at:
        while (true) {
            p = trail.last();
            confl = reason[var(p)];

            if (seen[var(p)]) {
              seen[var(p)] = 0;

              if (confl == NULL) {
                if (out_learnt[0] == lit_Undef) {
                  if (verbosity >= 2) printf("ASSERTING " L_LIT "\n", L_lit(~p));
                  out_learnt[0] = ~p;
                  out_learnt_final_size = out_learnt.size();
                  out_btlevel_final = out_btlevel;
                }

                undoOne(); if (trail_lim.last().first == trail.size()) undoOneLevel();
                goto resolved;
              }

              pathC--;

              if (pathC == 0 && out_learnt[0] == lit_Undef) {
                if (verbosity >= 2) printf("ASSERTING " L_LIT "\n", L_lit(~p));
                out_learnt[0] = ~p;
                out_learnt_final_size = out_learnt.size();
                out_btlevel_final = out_btlevel;
              }

              p_reason.clear();
              if (verbosity >= 2) {
                printf("CALC_REASON " L_LIT "\n", L_lit(p));
              }
              confl->calcReason(*this, p, p_reason);

              if (verbosity >= 2) {
                printf("REASON " L_LIT ":", L_lit(p));
                for (int i = 0; i < p_reason.size(); i++) {
                  printf(" " L_LIT, L_lit(p_reason[i]));
                }
                printf("\n");
              }

              undoOne(); if (trail_lim.last().first == trail.size()) undoOneLevel();
              break;
            }

            undoOne(); if (trail_lim.last().first == trail.size()) undoOneLevel();

            if (confl == NULL) {
              if (verbosity >= 2) printf("OLD_LEVEL\n");
              pathC = 0;
              int max_level = out_btlevel;
              out_btlevel = 0;

              if (max_level <= root_level) {
                for (int j = 1; j < out_learnt.size(); j++) seen[var(out_learnt[j])] = 0;
                return false;
              }

              for (int j = 1; j < out_learnt.size(); j++) {
                Lit lit = out_learnt[j];
                int lvl = level[var(lit)];
                if (lvl == max_level) {
                  pathC++;
                }
                else {
                  out_btlevel = max(out_btlevel, lvl);
                  if (pathC) out_learnt[j - pathC] = lit;
                }
              }

              out_learnt.shrink(pathC);
              out_learnt[0] = lit_Undef;
              cancelUntil(max_level);
            }
        }
    }

resolved:

    for (int j = 0; j < out_learnt.size(); j++) seen[var(out_learnt[j])] = 0;    // ('seen[]' is now cleared)

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wmaybe-uninitialized"
    out_learnt.shrink(out_learnt.size() - out_learnt_final_size);
    out_btlevel = out_btlevel_final;
#pragma GCC diagnostic pop

    if (verbosity >= 2){
        printf(L_IND "Learnt ", L_ind);
        printClause(out_learnt);
        printf(" at level %d\n", out_btlevel);
    }

    if (verbosity >= 2) printf("ANALYZED2\n");

    return true;
}


/*_________________________________________________________________________________________________
|
|  enqueue : (p : Lit) (from : Constr*)  ->  [bool]
|  
|  Description:
|    Puts a new fact on the propagation queue as well as immediately updating the variable's value.
|    Should a conflict arise, FALSE is returned.
|  
|  Input:
|    p    - The fact to enqueue
|    from - [Optional] Fact propagated from this (currently) unit clause. Stored in 'reason[]'.
|           Default value is NULL (no reason).
|  
|  Output:
|    TRUE if fact was enqueued without conflict, FALSE otherwise.
|________________________________________________________________________________________________@*/
bool Solver::enqueue(Lit p, Reason* from)
{
   if (value(p) != l_Undef){
        if (value(p) == l_False){
            // Conflicting enqueued assignment
            if (decisionLevel() == 0)
                ok = false;
            return false;
        }else{
            // Existing consistent assignment -- don't enqueue
            return true;
        }
    }else{
        // New fact -- store it.
        if (verbosity >= 2) printf(L_IND "bind(" L_LIT ")\n", L_ind, L_lit(p));
        assigns[var(p)] = toInt(lbool(!sign(p)));
        // printf("prop %d %d\n", var(p), assigns[var(p)]);
        level  [var(p)] = decisionLevel();
        reason [var(p)] = from;
        trail.push(p);
        propQ.insert(p);
        return true;
    }
}


/*_________________________________________________________________________________________________
|
|  propagate : [void]  ->  [Constr*]
|  
|  Description:
|    Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
|    otherwise NULL.
|  
|    Post-conditions:
|      * the propagation queue is empty, even if there was a conflict.
|________________________________________________________________________________________________@*/
Reason* Solver::propagate(void)
{
    if (verbosity >= 2) printf("PROPAGATE %d\n", propQ.size());
    Reason* confl = NULL;
    while (propQ.size() > 0){
        stats.propagations++;
        Lit           p  = propQ.dequeue();        // 'p' is enqueued fact to propagate.
        vec<Constr*>& ws = watches[index(p)];
        if (verbosity >= 2) printf("WS_LEN %d " L_LIT "\n", ws.size(), L_lit(p));
        bool          keep_watch;
        Constr        **i, **j;
        for (i = j = (Constr**)ws; confl == NULL && i < (Constr**)ws + ws.size(); i++){
            stats.inspects++;
            keep_watch = false;
            if (verbosity >= 2) {
              printf("PROP_IX %ld\n", i - (Constr**)ws);
              std::cout << std::flush;
            }
            Reason *confl2 = (*i)->propagate(*this, p, keep_watch);
            if (confl2)
                confl = confl2,
                propQ.clear();
            if (keep_watch) {
                *j++ = *i;
            } else if (verbosity >= 2) {
              printf("REMOVE_WATCH_PROP " L_LIT " %p\n", L_lit(p), *i);
            }
        }

        Constr **end = (Constr**)ws + ws.size();

        if (confl == NULL) {
          // Copy the remaining watches:
          while (i < end)
              *j++ = *i++;
        } else {
          while (i < end) {
              if (verbosity >= 2) printf("MOVE_WATCH_PROP %ld " L_LIT " %p\n", j - (Constr**)ws, L_lit(p), *i);
              (*i)->moveWatch(j - (Constr**)ws, p);
              *j++ = *i++;
          }
        }

        ws.shrink(i - j);
    }

    return confl;
}


/*_________________________________________________________________________________________________
|
|  reduceDB : ()  ->  [void]
|  
|  Description:
|    Remove half of the learnt clauses, minus the clauses locked by the current assignment. Locked
|    clauses are clauses that are reason to a some assignment.
|________________________________________________________________________________________________@*/
struct reduceDB_lt { bool operator () (Clause* x, Clause* y) { return x->activity() < y->activity(); } };
void Solver::reduceDB(void)
{
    int     i, j;
    double  extra_lim = cla_inc / learnts.size();    // Remove any clause below this activity

    sort(learnts, reduceDB_lt());
    for (i = j = 0; i < learnts.size() / 2; i++){
        if (!learnts[i]->locked(*this))
            learnts[i]->remove(*this);
        else
            learnts[j++] = learnts[i];
    }
    for (; i < learnts.size(); i++){
        if (!learnts[i]->locked(*this) && learnts[i]->activity() < extra_lim)
            learnts[i]->remove(*this);
        else
            learnts[j++] = learnts[i];
    }
    learnts.shrink(i - j);
}


/*_________________________________________________________________________________________________
|
|  simplifyDB : [void]  ->  [bool]
|  
|  Description:
|    Simplify all constraints according to the current top-level assigment (redundant constraints
|    may be removed altogether).
|________________________________________________________________________________________________@*/
void Solver::simplifyDB(void)
{
    if (!ok) return;    // GUARD (public method)
    assert(decisionLevel() == 0);

    if (propagate() != NULL){
        ok = false;
        return; }
    if (nAssigns() == last_simplify)
        return;

    last_simplify = nAssigns();

    for (int type = 0; type < 2; type++){
        vec<Constr*>& cs = type ? (vec<Constr*>&)learnts : constrs;

        int     j = 0;
        for (int i = 0; i < cs.size(); i++){
            if (cs[i]->simplify(*this))
                cs[i]->remove(*this);
            else
                cs[j++] = cs[i];
        }
        cs.shrink(cs.size()-j);
    }
}


/*_________________________________________________________________________________________________
|
|  search : (nof_conflicts : int) (nof_learnts : int) (params : const SearchParams&)  ->  [lbool]
|  
|  Description:
|    Search for a model the specified number of conflicts, keeping the number of learnt clauses
|    below the provided limit. NOTE! Use negative value for 'nof_conflicts' or 'nof_learnts' to
|    indicate infinity.
|  
|  Output:
|    'l_True' if a partial assigment that is consistent with respect to the clauseset is found. If
|    all variables are decision variables, this means that the clause set is satisfiable. 'l_False'
|    if the clause set is unsatisfiable. 'l_Undef' if the bound on number of conflicts is reached.
|________________________________________________________________________________________________@*/
lbool Solver::search()
{
    if (!ok) return l_False;    // GUARD (public method)
    // assert(root_level == decisionLevel());

    stats.starts++;
    int     conflictC = 0;
    var_decay = 1 / params.var_decay;
    cla_decay = 1 / params.clause_decay;

    for (;;){
        if (status != Solver_RUNNING) {
          if (status == Solver_PAUSED) {
            elapsed += chrono::steady_clock::now() - tic;
            runningMutex.unlock();
            pauseMutex.lock();
            runningMutex.lock();
            pauseMutex.unlock();
            tic = chrono::steady_clock::now();
          }
          if (status == Solver_CANCELLED) {
            throw Cancelled();
          }
        }
        Reason* confl = propagate();
        if (confl != NULL){
            // CONFLICT

            if (verbosity >= 2) printf(L_IND "**CONFLICT**\n", L_ind);
            stats.conflicts++; conflictC++;
            vec<Lit>    learnt_clause;
            int         backtrack_level;
            if (decisionLevel() <= root_level)
                return l_False;
            if (!analyze(confl, learnt_clause, backtrack_level))
                return l_False;
            cancelUntil(max(backtrack_level, root_level));
            record(learnt_clause);
            varDecayActivity(); claDecayActivity();

        }else{
            // NO CONFLICT

            if (nof_conflicts >= 0 && conflictC >= nof_conflicts){
                // Reached bound on number of conflicts:
                propQ.clear();
                cancelUntil(root_level);
                return l_Undef; }

            if (decisionLevel() == 0)
                // Simplify the set of problem clauses:
                simplifyDB(), assert(ok);

            if (nof_learnts >= 0 && learnts.size()-nAssigns() >= nof_learnts)
                // Reduce the set of learnt clauses:
                reduceDB();

            // New variable decision:
            stats.decisions++;

            if (!trie.guess(*this)) {
              Var next = order.select(params.random_var_freq);

              if (next == var_Undef){
                  // Model found:
                  model.clear();
                  model.growTo(nVars());
                  for (int i = 0; i < nVars(); i++) model[i] = value(i);

                  return l_True;
              }

              check(assume(Lit(next, true)));
            }
        }
    }
}


// Divide all variable activities by 1e100.
//
void Solver::varRescaleActivity(void)
{
    for (int i = 0; i < nVars(); i++)
        activity[i] *= 1e-100;
    var_inc *= 1e-100;
}


// Divide all constraint activities by 1e100.
//
void Solver::claRescaleActivity(void)
{
    for (int i = 0; i < learnts.size(); i++)
        learnts[i]->activity() *= 1e-20;
    cla_inc *= 1e-20;
}


/*_________________________________________________________________________________________________
|
|  solve : (assumps : const vec<Lit>&)  ->  [bool]
|  
|  Description:
|    Top-level solve. If using assumptions (non-empty 'assumps' vector), you must call
|    'simplifyDB()' first to see that no top-level conflict is present (which would put the solver
|    in an undefined state).
|________________________________________________________________________________________________@*/
bool Solver::solve(const vec<Lit>& assumps)
{
    root_level = 0;
    if (trie.root.elems.size() && trie.reset(*this)) return false;
    simplifyDB();
    if (!ok) return false;

    params.var_decay = 0.95;
    params.clause_decay = 0.999;
    params.random_var_freq = 0.02;

    nof_conflicts = 100;
    nof_learnts   = nConstrs() / 3;

    for (int i = 0; i < assumps.size(); i++) {
      if (!assume(assumps[i])) {
          propQ.clear();
          cancelUntil(0);
          return false;
      }
      ++root_level;
      if (propagate() != NULL) {
          propQ.clear();
          cancelUntil(0);
          return false;
      }
    }
    return true;
}

bool Solver::resume() {
    lbool   status = l_Undef;

    while (status == l_Undef){
        if (verbosity >= 1){
            printf("| %9d | %7d %8d | %7d %7d %8d %7.1f |\n",
                (int)stats.conflicts, nConstrs(), (int)stats.clauses_literals,
                (int)nof_learnts, nLearnts(), (int)stats.learnts_literals,
                (double)stats.learnts_literals/nLearnts());
            fflush(stdout);
        }
        status = search();
        nof_conflicts *= 1.5;
        nof_learnts   *= 1.1;
    }

    return status == l_True;
}

void Solver::reset() {
  cancelUntil(0);
}
