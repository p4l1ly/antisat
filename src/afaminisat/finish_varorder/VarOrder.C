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

#include "../Solver.h"
#include "VarOrder.h"

FinishVarOrder::FinishVarOrder(const vec<char>& ass) : assigns(ass) {}

// Then, signa should be set externally
void FinishVarOrder::init() { varinfos.resize(assigns.size()); }

void FinishVarOrder::undo(Solver &S) {
  vector<int> &snapshot = snapshots[--snapshot_count];
  for (int candidate: snapshot) candidates.push_back(candidate);
}

bool FinishVarOrder::select(Solver &S) {
  add_snapshot();
  int declevel = S.decisionLevel();
  if (verbosity >= 2) printf("FINISH_SELECT %d %lu\n", declevel, candidates.size());
  while (!candidates.empty()) {
    int cand = candidates.back();
    candidates.pop_back();

    VarInfo &varinfo = varinfos[cand];
    if (assigns[cand] == 0) {
      if (!S.assume(Lit(cand, varinfo.signum))) assert(false);
      S.undos.push_back(this);
      snapshots.back().push_back(cand);
      if (verbosity >= 2) printf("FINISH_SELECTED\n");
      return true;
    }
    int level = S.level[cand];
    if (level <= varinfo.skip_level) {
      varinfo.enqueued = false;
      varinfo.skip_level = -1;
      continue;
    }
    unsigned snapshot_ix = snapshots.size() - declevel + level;
    snapshots[snapshot_ix].push_back(cand);
  }
  S.undos.push_back(this);
  if (verbosity >= 2) printf("FINISH_DONE\n");
  return false;
}

void FinishVarOrder::add_snapshot() {
  if (snapshot_count == snapshots.size()) {
    snapshots.emplace_back();
    ++snapshot_count;
    return;
  }
  snapshots[snapshot_count++].clear();
}

void FinishVarOrder::skip(int var, int level) {
  VarInfo &varinfo = varinfos[var];
  varinfo.skip_level = level;
  if (!varinfo.enqueued) {
    varinfo.enqueued = true;
    candidates.push_back(var);
  }
}
