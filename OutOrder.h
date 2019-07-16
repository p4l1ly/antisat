#ifndef OutOrder_h
#define OutOrder_h

#include "SolverTypes.h"

//=================================================================================================


class OutOrder {
    const vec<char>& assigns;       // var->val. Pointer to external assignment table.
    const vec<bool>& pures;
    const vec<int>& output_map;
    vec<Lit> queue;
    int queue_ix;

public:
    OutOrder(
        const vec<char>& ass, const vec<bool>& pures_, const vec<int>& outs
    ) : assigns(ass), pures(pures_), output_map(outs), queue_ix(0)
    { }

    inline void newVar(Lit x);
    inline bool undo(Var x);
    inline Lit select(void);

};

void OutOrder::newVar(Lit x) {
    if (!pures[var(x)])
        queue.push(x);
}

bool OutOrder::undo(Var x) {
    // printf("undoing %d %d %d\n", queue_ix - 1, var(queue[queue_ix - 1]), x);
    int ix = output_map[x];

    if (ix != -1) {
      if (queue_ix > ix) queue_ix = ix;
      return true;
    }

    return false;
}

Lit OutOrder::select(void) {
    // printf("select %d %d\n", queue_ix, queue.size());
    while (queue_ix < queue.size()) {
        // printf("queue_ix %d %d\n", queue_ix, var(queue[queue_ix]));
        Lit lit = queue[queue_ix++];
        // printf("select2 %d %d %d\n", var(lit), sign(lit), toLbool(assigns[var(lit)]).toInt());
        if (toLbool(assigns[var(lit)]) == l_Undef)
            return lit;
    }

    return Lit(var_Undef);
}

//=================================================================================================
#endif
