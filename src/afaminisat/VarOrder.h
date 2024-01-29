#ifndef BubbleVarOrder_h
#define BubbleVarOrder_h

#include "SolverTypes.h"
#include <vector>
#include "Constraints.h"

class Solver;

using std::vector;
using std::pair;

//=================================================================================================

class BubbleVarOrder: Undoable {
    const vec<char>&    assigns;       // var->val. Pointer to external assignment table.
    const vec<double>&  activity;      // var->act. Pointer to external activity table.
    unsigned guess_line = 0;
    std::vector<unsigned> var_ixs;
    std::vector<unsigned> snapshots;
    std::vector<pair<int, int>> barriers;
    const unsigned max_bubble_moves = 5;
    const double tolerance_increase = 1.05;

public:
    std::vector<Var> order;
    double tolerance = 10.0;
    // double tolerance = std::numeric_limits<double>::infinity();

    BubbleVarOrder(const vec<char>& ass, const vec<double>& act) : assigns(ass), activity(act) { }

    inline void init(const vector<Var> &order_);
    void update(Var x, Solver &S);                  // Called when variable increased in activity.
    bool update0(int right, int right_ix, Solver &S, int declevel);                  // Called when variable increased in activity.
    void undo(Solver &S);                    // Called when variable is unassigned and may be selected again.
    bool select(Solver &S); // Selects a new, unassigned variable (or 'var_Undef' if none exists).
};


void BubbleVarOrder::init(const vector<Var> &order_) {
  order = order_;

  var_ixs.resize(assigns.size(), -1);
  unsigned i = 0;
  for (Var var: order) var_ixs[var] = i++;

  snapshots.reserve(order.size());
  barriers.resize(order.size(), pair(-1, -1));
}

//=================================================================================================
#endif
