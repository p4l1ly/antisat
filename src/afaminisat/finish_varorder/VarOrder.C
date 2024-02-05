#include "../Solver.h"
#include "VarOrder.h"

FinishVarOrder::FinishVarOrder(const vec<char>& ass) : assigns(ass) {}

// Then, signa should be set externally
void FinishVarOrder::init() { varinfos.resize(assigns.size()); }

void FinishVarOrder::undo(Solver &S) {
  vector<int> &snapshot = snapshots[--snapshot_count];
  for (int candidate: snapshot) candidates.push_back(candidate);
}

Lit FinishVarOrder::select(Solver &S) {
  int declevel = S.decisionLevel();
  if (verbosity >= 2) printf("FINISH_SELECT %d %lu\n", declevel, candidates.size());
  while (!candidates.empty()) {
    int cand = candidates.back();
    candidates.pop_back();

    VarInfo &varinfo = varinfos[cand];
    if (assigns[cand] == 0) {
      if (verbosity >= 2) printf("FINISH_SELECTED %d\n", cand);
      return Lit(cand, S.var_types[cand] != OUTPUT_POS);
    }
    int level = S.level[cand];
    if (level <= varinfo.skip_level) {
      varinfo.enqueued = false;
      varinfo.skip_level = -1;
      continue;
    }
    unsigned snapshot_ix = level - S.root_level;
    snapshots[snapshot_ix].push_back(cand);
  }
  if (verbosity >= 2) printf("FINISH_DONE\n");
  return lit_Undef;
}

// TODO
// S.undos.push_back(this);
// snapshots.back().push_back(cand);

void FinishVarOrder::after_select(Solver &S) {
  if (snapshot_count == snapshots.size()) {
    snapshots.emplace_back();
    ++snapshot_count;
    return;
  }
  snapshots[snapshot_count++].clear();
  S.undos.push_back(this);
}

void FinishVarOrder::skip(int var, int level) {
  VarInfo &varinfo = varinfos[var];
  varinfo.skip_level = level;
  if (!varinfo.enqueued) {
    varinfo.enqueued = true;
    candidates.push_back(var);
  }
}
