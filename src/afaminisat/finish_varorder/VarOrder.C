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
      VarType var_type = S.var_types[cand];
      bool signum = var_type == OUTPUT_POS ? false : true;
      if (!S.assume(Lit(cand, signum))) assert(false);
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
