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

#ifndef Solver_h
#define Solver_h

#include <climits>
#include <cstring>
#include <iostream>
#include <atomic>
#include <mutex>
#include <chrono>

#include "SolverTypes.h"
#include "Constraints.h"
#include "Queue.h"
#include "VarOrder.h"
#include "Trie.h"

#define L_IND    "%-*d"
#define L_ind    3,decisionLevel()

void check(bool expr);

//=================================================================================================
// Solver -- the main class:


struct SolverStats {
    int64   starts, decisions, propagations, inspects, conflicts;
    int64   clauses, clauses_literals, learnts, learnts_literals;
    SolverStats(void) : starts(0), decisions(0), propagations(0), inspects(0), conflicts(0)
        , clauses(0), clauses_literals(0), learnts(0), learnts_literals(0) { }
};


struct SearchParams {
    double  var_decay, clause_decay, random_var_freq;    // (reasonable values are: 0.95, 0.999, 0.02)    
    SearchParams(double v = 1, double c = 1, double r = 0) : var_decay(v), clause_decay(c), random_var_freq(r) { }
};

#define Solver_RUNNING 0
#define Solver_PAUSED 1
#define Solver_CANCELLED 2
#define Solver_INIT 3

class Cancelled {
};

class Solver {
public:
    bool                ok;             // If FALSE, the constraints are already unsatisfiable. No part of the solver state may be used!
    std::atomic_int     status;
    std::mutex          runningMutex;
    std::mutex          pauseMutex;

    vec<Constr*>        constrs;        // List of problem constraints.
    vec<Clause*>        learnts;        // List of learnt clauses.
    double              cla_inc;        // Amount to bump next clause with.
    double              cla_decay;      // INVERSE decay factor for clause activity: stores 1/decay.

    vec<double>         activity;       // A heuristic measurement of the activity of a variable.
    double              var_inc;        // Amount to bump next variable with.
    double              var_decay;      // INVERSE decay factor for variable activity: stores 1/decay. Use negative value for static variable order.

    vec<bool>           pures;          // The pure literals (undef === one).
    vec<int>            output_map;    // The mask of output variables.
    vec<Lit>            outputs;        // The output literals.
    std::unordered_set<unsigned> finals;        // The output literals.
    std::vector<Lit> posq_outputs;        // The output literals.

    VarOrder            order;          // Keeps track of the decision variable order.

    vec<vec<Constr*> >  watches;        // 'watches[lit]' is a list of constraints watching 'lit' (will go there if literal becomes true).
    std::vector<Undoable*> undos;

    Queue<Lit>          propQ;          // Propagation queue.

    vec<char>           assigns;        // The current assignments (lbool:s stored as char:s).
    vec<Lit>            trail;          // List of assignments made. 
    vec<std::pair<int, int>>            trail_lim;      // Separator indices for different decision levels in 'trail'.
    vec<Reason*>        reason;         // 'reason[var]' is the clause that implied the variables current value, or 'NULL' if none.
    vec<int>            level;          // 'level[var]' is the decision level at which assignment was made.
    int                 root_level;     // Level of first proper decision.
    int                 last_simplify;  // Number of top-level assignments at last 'simplifyDB()'.

    SearchParams params;
    double nof_conflicts, nof_learnts;

    Trie trie;

    chrono::duration<double> elapsed = chrono::duration<double>::zero();
    chrono::time_point<chrono::steady_clock> tic;

    // Temporaries (to reduce allocation overhead):
    //
    vec<char>           analyze_seen;
    vec<Lit>            analyze_toclear;

    // Main internal methods:
    //
    bool        assume       (Lit p);
    void        undoOne      (void);
    void        undoOneLevel (void);
    void        cancel       (void);
    void        cancelUntil  (int level);
    void        record       (const vec<Lit>& clause);

    bool        analyze      (Reason* confl, vec<Lit>& out_learnt, int& out_btlevel); // (bt = backtrack)
    bool        analyze2     (const vector<int>&, vec<Lit>& out_learnt, int& out_btlevel); // (bt = backtrack)
    bool        enqueue      (Lit fact, Reason* from = NULL);
    Reason*     propagate    (void);
    void        reduceDB     (void);
    lbool       search       ();

    // Activity:
    //
    void    varBumpActivity(Lit p) {
        if (var_decay < 0) return;     // (negative decay means static variable order -- don't bump)
        if ( (activity[var(p)] += var_inc) > 1e100 ) varRescaleActivity();
        order.update(var(p), *this);
    }

    void    varDecayActivity(void) {
      if (var_decay >= 0) {
        var_inc *= var_decay;
        order.tolerance *= var_decay;
      }
    }
    void    varRescaleActivity(void);

    void    claBumpActivity(Clause* c) { if ( (c->activity() += cla_inc) > 1e20 ) claRescaleActivity(); }
    void    claDecayActivity(void) { cla_inc *= cla_decay; }
    void    claRescaleActivity(void);

    int     decisionLevel(void) { return trail_lim.size(); }

public:
    Solver()
      : ok(true)
      , status(Solver_INIT)
      , cla_inc(1)
      , cla_decay(1)
      , var_inc(1)
      , var_decay(1)
      , order(assigns, activity, pures, output_map)
      , last_simplify(-1)
      , params(1, 1, 0)
      {
        runningMutex.lock();
    }

    ~Solver();

    // Helpers: (semi-internal)
    //
    lbool   value(Var x) { return toLbool(assigns[x]); }
    lbool   value(Lit p) { return sign(p) ? ~toLbool(assigns[var(p)]) : toLbool(assigns[var(p)]); }

    int     nAssigns(void) { return trail.size(); }
    int     nConstrs(void) { return constrs.size(); }
    int     nLearnts(void) { return learnts.size(); }

    // Statistics: (read-only member variable)
    //
    SolverStats stats;

    // Problem specification:
    //
    Var     newVar (bool pure=false);
    int     nVars  (void)  { return assigns.size(); }
    void    addUnit(Lit p) { if (ok) enqueue(p); }

    // -- constraints:
    friend class Clause;
    friend class UpwardClause;
    friend bool Clause_new(Solver& S, const vec<Lit>& ps, bool learnt, Clause*& out_clause);
    friend bool UpwardClause_new(Solver& S, Lit p, const vec<Lit>& ps, UpwardClause*& out_clause);

    void  addClause(const vec<Lit>& ps) {
      if (ok){
        Clause* c;
        ok = Clause_new(*this, ps, false, c);
        if (verbosity >= 2) printf("ADD_CLAUSE %p %p\n", c, c ? c->getSpecificPtr2() : c);
        if (c != NULL) constrs.push(c);
      }
    }

    void  addUpwardClause(Lit out, const vec<Lit>& ps) {
      if (ok){
        UpwardClause* c;
        ok = UpwardClause_new(*this, out, ps, c);
        if (verbosity >= 2) printf("ADD_UPWARD_CLAUSE %p %p\n", c, c ? c->getSpecificPtr2() : c);
        if (c != NULL) constrs.push(c);
      }
    }

    void addConstr(Constr *c) {
      constrs.push(c);
    }

    bool onSatConflict(const vector<int>& cell);

    // Solving:
    //
    bool    okay(void) { return ok; }
    void    simplifyDB(void);
    bool    solve(const vec<Lit>& assumps);
    bool    solve(void) { vec<Lit> tmp; return solve(tmp); }
    bool resume();
    void reset();

    vec<lbool>  model;              // If problem is solved, this vector contains the model (if any).
};



// Revert one variable binding on the trail.
//
inline void Solver::undoOne(void)
{
    if (verbosity >= 2){ Lit p = trail.last(); printf(L_IND "unbind(" L_LIT ")\n", L_ind, L_lit(p)); }
    Var     x  = var(trail.last()); trail.pop();
    assigns[x] = toInt(l_Undef);
    reason [x] = NULL;
}

//=================================================================================================
#endif
