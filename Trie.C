#include <algorithm>
#include <iostream>
#include <utility>
#include <boost/iterator/transform_iterator.hpp>


#include "Trie.h"

using std::cout;

void Trie::watch(Solver &S, int var_) {
  // optimized but opaque way to tell: watch(Lit(var)); watch(~Lit(var))
  var_ += var_;
  if (!watch_mask[var_]) {
    watch_mask[var_] = true;
    S.watches[var_].push(this);
  }
  var_++;
  if (!watch_mask[var_]) {
    watch_mask[var_] = true;
    S.watches[var_].push(this);
  }
}

void BackJumper::undo(Solver &S, Lit _p) {
  S.trie->active_hor = active_hor;
  S.trie->hor_ix = hor_ix;
  S.trie->ver_ix = ver_ix;
  S.trie->my_zeroes.erase(
      S.trie->my_zeroes.begin() + my_zeroes_size,
      S.trie->my_zeroes.end()
  );

  if (verbosity >= 2) printf("UNDO %d %d %lu\n", hor_ix, ver_ix, active_hor->vers->size());
  Lit out_lit = S.outputs[ver_ix >= 0
    ? (*(*active_hor->vers)[hor_ix].hors)[ver_ix].tag
    : (*active_hor->vers)[hor_ix].tag
  ];
  S.trie->watch(S, var(out_lit));
  if (verbosity >= 2) printf("WU " L_LIT "\n", L_lit(out_lit));
}

Trie::Trie(unsigned var_count_, int index_count)
: root(NULL),
  var_count(var_count_),
  back_ptrs(var_count_),
  my_zeroes(),
  propagations(),
  acc_backjumpers(var_count_),
  watch_mask(index_count)
{
  my_zeroes.reserve(var_count_);
  propagations.reserve(var_count_);
  active_hor = &root;
}


// TODO (optional) support impure_outputs
Lit Trie::guess(Solver &S) {
  if (ver_ix != -1) {
    HorHead &hor_head = (*(*active_hor->vers)[hor_ix].hors)[ver_ix];
    Lit out_lit = S.outputs[hor_head.tag];

    hor_head.backjumper->my_zeroes_size = my_zeroes.size();
    S.undos[var(out_lit)].push(hor_head.backjumper);
    if (verbosity >= 2) printf("GUESS_VER %d %d %d " L_LIT "\n", hor_ix, ver_ix, hor_head.tag, L_lit(out_lit));
    return out_lit;
  }
  if (hor_ix < active_hor->vers->size()) {
    VerHead &ver_head = (*active_hor->vers)[hor_ix];
    Lit out_lit = S.outputs[ver_head.tag];

    ver_head.backjumper->my_zeroes_size = my_zeroes.size();
    S.undos[var(out_lit)].push(ver_head.backjumper);
    if (verbosity >= 2) printf("GUESS_HOR %d %d %d " L_LIT "\n", hor_ix, ver_ix, ver_head.tag, L_lit(out_lit));
    return out_lit;
  }
  else {
    if (active_var == var_count) return lit_Undef;
    active_var_old = active_var;

    while (active_var < var_count) {
      Lit p = S.outputs[active_var];
      if (S.value(p) == l_Undef) {
        if (verbosity >= 2) printf("GUESS_ACC %d " L_LIT "\n", active_var, L_lit(p));
        S.undos[var(p)].push(this);
        back_ptrs[active_var] = active_var_old;
        active_var++;
        return p;
      }
      active_var++;
    }
    S.undos[var(S.trail.last())].push(&active_var_undo);
    if (verbosity >= 2) printf("noguess %d\n", active_var_old);
    return lit_Undef;
  }
}

inline unsigned pair_snd(const std::pair<int, unsigned> &x) {
  return x.second;
}

BackJumper* Trie::onSat(Solver &S) {
  if (verbosity >= 2) printf("ON_SAT\n");
  S.stats.conflicts++;

  unordered_set<unsigned> my_zeroes_set(my_zeroes.begin(), my_zeroes.end());

  int max_level = -1;
  vector<std::pair<int, unsigned>> added_vars;
  for (unsigned x = 0; x < var_count; x++) {
    if (S.value(S.outputs[x]) == l_False) {
      max_level = max(max_level, S.level[var(S.outputs[x])]);
      if (!my_zeroes_set.contains(x)) {
        added_vars.emplace_back(S.level[var(S.outputs[x])], x);
      }
    }
  }

  if (verbosity >= 2) printf("MAX_LEVEL %d\n", max_level);

  if (added_vars.size() == 0) {
    if (verbosity >= 2) printf("NO_ADDED_VAR\n");
    BackJumper *back = active_hor->back;
    S.cancelUntil(max_level);
    return back;
  }

  max_level = max(max_level, std::get<0>(added_vars.back()));

  std::sort(added_vars.begin(), added_vars.end());

  if (verbosity >= 2) {
    for (auto x: added_vars) {
       printf("ADDED_VAR %d %d " L_LIT "\n", std::get<0>(x), std::get<1>(x), L_lit(S.outputs[std::get<1>(x)]));
     }
  }

  unsigned parent_hor_ix = active_hor->vers->size();

  const std::pair<int, unsigned>& x = added_vars[0];
  VerHead &ver_head = active_hor->vers->emplace_back(x.second, active_hor, hor_ix, -1);

  ver_head.hors->reserve(var_count - my_zeroes.size());

  for (unsigned i = 1; i < added_vars.size(); i++) {
    ver_head.hors->emplace_back(added_vars[i].second, active_hor, parent_hor_ix, i - 1);
  }

  unsigned i = added_vars.size() - 1;
  const std::pair<int, unsigned>* x_pre = &added_vars[i];

  BackJumper *last_backjumper = NULL;

  for (unsigned acc_ptr = active_var_old; acc_ptr--; acc_ptr = back_ptrs[acc_ptr]) {
    int svar = var(S.outputs[acc_ptr]);
    int lvl = S.level[svar];
    if (lvl <= last_state_level) break;

    if (verbosity >= 0) printf("LVL %d %d " L_LIT " %d\n", lvl, acc_ptr, L_lit(S.outputs[acc_ptr]), back_ptrs[acc_ptr]);

    while (true) {
      const std::pair<int, unsigned>& x = *x_pre;
      if (x.first < lvl) {
        acc_backjumpers[acc_ptr] = last_backjumper;
        break;
      }

      if (verbosity >= 0) printf("I %d\n", i);

      if (i == 0) {
        ver_head.backjumper->my_zeroes_size = my_zeroes.size();
        acc_backjumpers[acc_ptr] = ver_head.backjumper;
        break;
      }

      i--;
      x_pre = &added_vars[i];

      assert(x.first == lvl);
      if (x_pre->first < lvl) {
        HorHead &hor_head = (*ver_head.hors)[i];
        hor_head.backjumper->my_zeroes_size = my_zeroes.size() + i + 1;
        last_backjumper = acc_backjumpers[acc_ptr] = hor_head.backjumper;
      }
    }
  }

  auto beg = boost::make_transform_iterator(added_vars.begin(), pair_snd);
  auto end = boost::make_transform_iterator(added_vars.end(), pair_snd);
  my_zeroes.reserve(my_zeroes.size() + added_vars.size());
  my_zeroes.insert(my_zeroes.end(), beg, end);

  S.cancelUntil(max_level);
  return NULL;
}

void BackJumper::cut() {
  vector<HorHead> &hors = *(*active_hor->vers)[hor_ix].hors;
  if (verbosity >= 2) printf("CUTTING [%d] AT %d\n", hor_ix, ver_ix);
  hors.erase(hors.begin() + ver_ix, hors.end());
}


void Trie::remove(Solver& S, bool just_dealloc) {
  std::cerr << "SubsetQ removed!\n";
}

bool Trie::simplify(Solver& S) {
  return false;
}


WhatToDo Trie::after_hors_change(Solver &S) {
  if (hor_ix == active_hor->vers->size()) {
    return WhatToDo::DONE;
  }

  VerHead &ver_head = (*active_hor->vers)[hor_ix];
  int out = ver_head.tag;
  lbool val = S.value(S.outputs[out]);

  if (val == l_Undef) {
    if (ver_head.hors->size() == 0) return WhatToDo::PROPAGATE;
    return WhatToDo::WATCH;
  }
  if (val == l_False && ver_head.hors->size() == 0) {
    my_zeroes.push_back(out);
    return WhatToDo::CONFLICT;
  }
  return WhatToDo::AGAIN;
}


WhatToDo Trie::after_vers_change(Solver &S) {
  VerHead &ver_head = (*active_hor->vers)[hor_ix];
  int out = (*ver_head.hors)[ver_ix].tag;
  if (verbosity >= 2) printf("OUT %d\n", out);
  lbool val = S.value(S.outputs[out]);

  if (val == l_Undef) {
    if (ver_ix == int(ver_head.hors->size()) - 1) {
      return WhatToDo::PROPAGATE;
    }
    return WhatToDo::WATCH;
  }
  if (val == l_False && ver_ix == int(ver_head.hors->size()) - 1) {
    my_zeroes.push_back(out);
    return WhatToDo::CONFLICT;
  }
  return WhatToDo::AGAIN;
}


bool Trie::propagate(Solver& S, Lit p, bool& keep_watch) {
  if (verbosity >= 2) printf("PROP %d %d " L_LIT "\n", hor_ix, ver_ix, L_lit(p));

  watch_mask[index(p)] = false;
  if (hor_ix >= active_hor->vers->size()) return true;

  unsigned out = ver_ix >= 0
    ? (*(*active_hor->vers)[hor_ix].hors)[ver_ix].tag
    : (*active_hor->vers)[hor_ix].tag;
  Lit out_lit = S.outputs[out];

  if (var(out_lit) != var(p)) return true;

  WhatToDo what_to_do;

  while (true) {
    if (ver_ix != -1) {
      if (S.value(out_lit) == l_True) {
        HorHead &hor_head = (*(*active_hor->vers)[hor_ix].hors)[ver_ix];
        active_hor = hor_head.hor;
        hor_ix = 0;
        ver_ix = -1;
        what_to_do = after_hors_change(S);
      }
      else {
        my_zeroes.push_back(out);
        ver_ix++;
        what_to_do = after_vers_change(S);
      }
    }
    else {
      if (S.value(out_lit) == l_True) {
        hor_ix++;
        what_to_do = after_hors_change(S);
      }
      else {
        my_zeroes.push_back(out);
        ver_ix++;
        what_to_do = after_vers_change(S);
      }
    }

    switch (what_to_do) {
      case AGAIN: {
        if (verbosity >= 2) printf("AGAIN %d %d\n", hor_ix, ver_ix);
        out = ver_ix >= 0
          ? (*(*active_hor->vers)[hor_ix].hors)[ver_ix].tag
          : (*active_hor->vers)[hor_ix].tag;
        out_lit = S.outputs[out];
        continue;
      }

      case WATCH: {
        if (verbosity >= 2) printf("WATCH %d %d\n", hor_ix, ver_ix);
        out_lit = S.outputs[ver_ix != -1
          ? (*(*active_hor->vers)[hor_ix].hors)[ver_ix].tag
          : (*active_hor->vers)[hor_ix].tag
        ];
        watch(S, var(out_lit));
        if (verbosity >= 2) printf("WW " L_LIT "\n", L_lit(out_lit));
        return true;
      }

      case DONE: {
        if (verbosity >= 2) printf("DONE %d %d, active_var: %d\n", hor_ix, ver_ix, active_var);
        last_state_level = S.decisionLevel();
        return true;
      }

      case PROPAGATE: {
        if (verbosity >= 2) printf("PROPAGATE %d %d\n", hor_ix, ver_ix);
        out_lit = S.outputs[ver_ix != -1
          ? (*(*active_hor->vers)[hor_ix].hors)[ver_ix].tag
          : (*active_hor->vers)[hor_ix].tag
        ];

        watch(S, var(out_lit));
        if (verbosity >= 2) printf("WP " L_LIT "\n", L_lit(out_lit));

        propagations.push_back(my_zeroes.size());
        S.undos[var(out_lit)].push(&prop_undo);
        return S.enqueue(out_lit, this);
      }

      case CONFLICT: {
          if (verbosity >= 2) printf("CONFLICT %d %d\n", hor_ix, ver_ix);
          return false;
      }
    }
  }
}


void Trie::undo(Solver& S, Lit p) {
  active_var--;
  if (acc_backjumpers[active_var] != NULL) {
    if (verbosity >= 2) printf("ACC_UNDO_BACKJUMP\n");
    acc_backjumpers[active_var]->undo(S, lit_Undef);
    acc_backjumpers[active_var] = NULL;
  }

  active_var = back_ptrs[active_var];
  if (verbosity >= 2) printf("ACC_UNDO %d " L_LIT "\n", active_var, L_lit(p));
}


void Trie::calcReason(Solver& S, Lit p, vec<Lit>& out_reason) {
  if (p == lit_Undef) {
    int max_level = -1;
    for (unsigned x: my_zeroes) {
      Lit out_lit = S.outputs[x];
      max_level = max(max_level, S.level[var(out_lit)]);
      out_reason.push(~out_lit);
    }
    S.cancelUntil(max_level);
  }
  else {
    if (verbosity >= 2) printf("PROPS %lu\n", propagations.size());
    unsigned my_zeroes_size = propagations.back();

    for (unsigned i = 0; i < my_zeroes_size; i++) {
      out_reason.push(~S.outputs[my_zeroes[i]]);
    }
  }

  if (verbosity >= 2) {printf("CALC_REASON " L_LIT, L_lit(p)); for (unsigned x: my_zeroes) { printf(" %u", x); } printf("\n");}
}


void Trie::reset(Solver &S) {
  active_hor = &root;
  hor_ix = 0;
  ver_ix = -1;
  active_var = 0;
  active_var_old = 0;
  propagations.clear();
  my_zeroes.clear();

  if (verbosity >= 2) printf("RESET\n");

  if (root.vers->size()) {
    Lit out_lit = S.outputs[(*root.vers)[0].tag];
    watch(S, var(out_lit));
    if (verbosity >= 2) printf("WR " L_LIT "\n", L_lit(out_lit));
  }
}

void PropUndo::undo(Solver &S, Lit _p) { S.trie->propagations.pop_back(); }
void ActiveVarUndo::undo(Solver &S, Lit _p) { S.trie->active_var = S.trie->active_var_old; }
