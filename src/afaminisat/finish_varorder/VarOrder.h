#ifndef FinishVarOrder_h
#define FinishVarOrder_h

#include "../SolverTypes.h"
#include "../Solver.h"
#include <vector>
#include "../Constraints.h"

class Solver;

using std::vector;
using std::pair;

//=================================================================================================

struct VarInfo {
  bool enqueued = false;
  int skip_level = -1;
};

class FinishVarOrder: public Undoable {
    const vec<char>&    assigns;       // var->val. Pointer to external assignment table.
    vector<vector<int>> snapshots;
    unsigned snapshot_count = 0;
    vector<int> candidates;
    vector<VarInfo> varinfos;

public:

    FinishVarOrder(const vec<char>& ass);

    void init(); // Then, signa should be set externally
    void undo(Solver &S);
    bool select(Solver &S);
    void add_snapshot();
    void skip(int var, int level);
};


//=================================================================================================
#endif
