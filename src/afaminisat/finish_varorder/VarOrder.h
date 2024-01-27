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
  bool signum = false;
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
