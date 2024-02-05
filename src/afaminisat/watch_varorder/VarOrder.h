#ifndef WatchVarOrder_h
#define WatchVarOrder_h

#include "../SolverTypes.h"
#include <vector>
#include "../Constraints.h"

class Solver;

using std::vector;
using std::pair;

//=================================================================================================

struct WatchInfo {
  unsigned pos_watch_count;
  unsigned neg_watch_count;
  bool skipped;
  bool enqueued;
};

class WatchVarOrder: Undoable {
    const vec<char>&    assigns;       // var->val. Pointer to external assignment table.
    const vec<double>&  activity;      // var->act. Pointer to external activity table.
    std::vector<unsigned> var_ixs;
    std::vector<unsigned> snapshots;
    std::vector<pair<int, int>> barriers;
    std::vector<WatchInfo> watch_infos;
    std::vector<int> skipped_candidates;
    const unsigned max_bubble_moves = 5;
    const double tolerance_increase = 1.05;
#ifdef AFA
#ifdef WATCH_VARORDER
    const bool finishing;
#endif
#endif

public:
    unsigned guess_line = 0;
    std::vector<Var> order;
    double tolerance = 10.0;
    // double tolerance = std::numeric_limits<double>::infinity();

    WatchVarOrder(const vec<char>& ass, const vec<double>& act, bool finishing_)
    : assigns(ass), activity(act)
#ifdef AFA
#ifdef WATCH_VARORDER
    , finishing(finishing_)
#endif
#endif
    { }

    inline void init(const vector<Var> &order_);
    void update(Var x, Solver &S);                  // Called when variable increased in activity.
    bool update0(int right, int right_ix, Solver &S);                  // Called when variable increased in activity.
    void undo(Solver &S);                    // Called when variable is unassigned and may be selected again.
    Lit select(Solver &S); // Selects a new, unassigned variable (or 'var_Undef' if none exists).
    void noselect(Solver &S);
    void after_select(int old_guess_line, Solver &S);
    void watch(Lit lit);
    void unwatch(Lit lit);
};

void WatchVarOrder::init(const vector<Var> &order_) {
  order = order_;

  var_ixs.resize(assigns.size(), -1);
  unsigned i = 0;
  for (Var var: order) var_ixs[var] = i++;

  snapshots.reserve(order.size());
  barriers.resize(order.size(), pair(-1, -1));

  watch_infos.resize(assigns.size());
}

//=================================================================================================
#endif
