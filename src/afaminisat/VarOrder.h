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

#ifndef VarOrder_h
#define VarOrder_h

#include "SolverTypes.h"
#include <vector>
#include "Constraints.h"

class Solver;

//=================================================================================================

extern unsigned global_bubble_move_count;
extern unsigned global_bubble_move_count_undo;

class VarOrder: Undoable {
    const vec<char>&    assigns;       // var->val. Pointer to external assignment table.
    const vec<double>&  activity;      // var->act. Pointer to external activity table.
    const vec<bool>&    pures;
    const vec<int>&     output_map;
    double              random_seed;   // For the internal random number generator
    std::vector<Var> order;
    unsigned guess_line = -1;
    std::vector<unsigned> var_ixs;
    std::vector<unsigned> snapshots;
    std::vector<int> barriers;
    const unsigned max_bubble_moves = 5;
    // const double tolerance_decrease = 0.9999995;

    const double tolerance_decrease = 0.999;
    const double tolerance_increase = 1.05;
    //
    // const double tolerance_decrease = 1.0;
    // const double tolerance_increase = 1.0;

    const unsigned min_bubble_move_count_since_last_stage = 1;
    const unsigned min_update_count_since_last_stage = 5;

public:
    double tolerance = 10.0;
    // double tolerance = std::numeric_limits<double>::infinity();

    unsigned bubble_move_count_since_last_stage = 0;
    unsigned update_count_since_last_stage = 0;

    VarOrder(
        const vec<char>& ass, const vec<double>& act, const vec<bool>& pures_,
        const vec<int>& outs
    ) : assigns(ass), activity(act), pures(pures_), output_map(outs),
        random_seed(91648253), order(), snapshots(), barriers(), var_ixs()
    { }

    inline void newVar(void);
    inline void init(void);
    void update(Var x, Solver &S);                  // Called when variable increased in activity.
    void undo(Solver &S);                    // Called when variable is unassigned and may be selected again.
    Var select(double random_freq, Solver &S); // Selects a new, unassigned variable (or 'var_Undef' if none exists).
    void new_stage() {
      if (
        bubble_move_count_since_last_stage < min_bubble_move_count_since_last_stage
        && update_count_since_last_stage >= min_update_count_since_last_stage
      ) {
        if (verbosity >= -3) {
          printf("TOLERANCE_DECREASE %g %g\n", tolerance, tolerance * tolerance_decrease);
        }
        tolerance *= tolerance_decrease;
      }

      bubble_move_count_since_last_stage = 0;
      update_count_since_last_stage = 0;
    }
};


void VarOrder::newVar(void)
{
    int ix = assigns.size() - 1;
    // printf("pure1 %d %d %d\n", ix, pures[ix], output_map[ix]);
    if (!pures[ix] && output_map[ix] == -1) {
        order.push_back(ix);
    }
}


void VarOrder::init() {
  if (order.empty()) return;

  var_ixs.resize(assigns.size(), -1);
  unsigned i = 0;
  for (Var var: order) var_ixs[var] = i++;

  snapshots.reserve(order.size());
  barriers.resize(order.size(), -1);
}

//=================================================================================================
#endif
