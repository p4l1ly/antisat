#include <algorithm>
#include <iostream>
#include <utility>
#include <boost/iterator/transform_iterator.hpp>


#include "Trie.h"

int hor_head_count = 0;
int hor_count = 0;
int ver_count = 0;

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

Trie::Trie(unsigned var_count_, int index_count)
: root()
, var_count(var_count_)
, back_ptrs(var_count_)
, my_zeroes()
, propagations()
, acc_backjumpers(var_count_)
, watch_mask(index_count)
, backjumpers()
, knees()
{
  my_zeroes.reserve(var_count_);
  propagations.reserve(var_count_);
  backjumpers.reserve(var_count_);
  knees.reserve(var_count_);
  active_hor = &root;
}


// TODO (optional) support impure_outputs
Lit Trie::guess(Solver &S) {
  if (!move_right && ver_ix != -1) {
    HorHead &hor_head = (*(*active_hor)[hor_ix].hors)[ver_ix];
    Lit out_lit = S.outputs[hor_head.tag];

    backjumpers.emplace_back(active_hor, hor_ix, ver_ix, my_zeroes.size(), knees.size());
    S.undos[var(out_lit)].push(&backjumper_undo);

    if (verbosity >= 2) printf("GUESS_VER %d %d %d " L_LIT "\n", hor_ix, ver_ix, hor_head.tag, L_lit(out_lit));
    return out_lit;
  }
  if (!move_right && hor_ix < active_hor->size()) {
    VerHead &ver_head = (*active_hor)[hor_ix];
    Lit out_lit = S.outputs[ver_head.tag];

    backjumpers.emplace_back(active_hor, hor_ix, ver_ix, my_zeroes.size(), knees.size());
    S.undos[var(out_lit)].push(&backjumper_undo);

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
    S.undos[var(S.trail.last())].push(&active_var_done_undo);
    if (verbosity >= 2) printf("noguess %d\n", active_var_old);
    return lit_Undef;
  }
}

inline unsigned pair_snd(const std::pair<int, unsigned> &x) {
  return x.second;
}

CutKnee Trie::onSat(Solver &S) {
  if (verbosity >= 2) printf("ON_SAT\n");

  unordered_set<unsigned> my_zeroes_set(my_zeroes.begin(), my_zeroes.end());

  // max level of added_vars+my_zeroes
  int max_level = -1;

  // added_vars are (level, variable) pairs, of zero variables added in the
  // accepting condition (= not included in my_zeroes)
  vector<std::pair<int, unsigned>> added_vars;
  added_vars.reserve(var_count);
  for (unsigned x = 0; x < var_count; x++) {
    if (S.value(S.outputs[x]) == l_False) {
      int lvl = S.level[var(S.outputs[x])];
      max_level = max(max_level, lvl);
      if (!my_zeroes_set.contains(x)) {
        added_vars.emplace_back(lvl, x);
      }
    }
  }

  if (verbosity >= 2) printf("MAX_LEVEL %d\n", max_level);

  // We have found a solution that covers the last traversed clause => we
  // shrink the clause (cut it up to the knee) instead of adding a new branch
  // to the trie.
  if (added_vars.size() == 0) {
    if (verbosity >= 2) printf("NO_ADDED_VAR\n");
    CutKnee result(knees.back());
    S.cancelUntil(max_level);
    return result;
  }

  // sort added_vars by level
  std::sort(added_vars.begin(), added_vars.end());

  if (verbosity >= 2) {
    for (auto x: added_vars) {
       printf("ADDED_VAR %d %d " L_LIT "\n", std::get<0>(x), std::get<1>(x), L_lit(S.outputs[std::get<1>(x)]));
     }
  }

  const std::pair<int, unsigned>& x = added_vars[0];

  if (move_right) {
    // We create a new horizontal empty branch right to the current final place
    // (which is vertical because move_right is set only when accepting at
    // vertical places).
    move_right = false;
    vector<VerHead> *new_active_hor = new vector<VerHead>();
    if (verbosity >= -2) hor_count++;
    (*(*active_hor)[hor_ix].hors)[ver_ix].vers = new_active_hor;
    active_hor = new_active_hor;
    hor_ix = 0;
    ver_ix = -1;
  }

  // Add the first added_var to the current horizontal branch.
  VerHead &ver_head = active_hor->emplace_back(x.second);
  ver_head.hors->reserve(added_vars.size() - 1);

  // Continue down with a vertical branch containing the remaining added_vars.
  ver_head.hors->reserve(added_vars.size() - 1);
  for (unsigned i = 1; i < added_vars.size(); i++) {
    ver_head.hors->emplace_back(added_vars[i].second);
  }

  unsigned i = added_vars.size();

  // We go from the lastly guessed variable to the firstly guessed one.
  // To each guessed variable, we assign a backjumper that points to the
  // latest place with a level lower than the level of the guessed variable.
  //
  // Why is this so complicated? Shouldn't that always be just the added_var
  // immediately before the guessed added var? No because guessed variables are
  // of course not in added_vars, as they are 1-valued.
  for (unsigned acc_ptr = active_var_old; acc_ptr--; acc_ptr = back_ptrs[acc_ptr]) {
    int svar = var(S.outputs[acc_ptr]);
    int lvl = S.level[svar];

    // How could this be even possible? If the new branch is added, the list
    // of the guessed variables does not get fully erased in the conflict
    // triggered by the new branch.
    if (lvl <= last_state_level) break;

    if (verbosity >= 0) printf("LVL %d %d " L_LIT " %d\n", lvl, acc_ptr, L_lit(S.outputs[acc_ptr]), back_ptrs[acc_ptr]);

    while (true) {
      const std::pair<int, unsigned>& x = added_vars[i - 1];
      if (x.first < lvl) {
        if (i != added_vars.size()) {
          acc_backjumpers[acc_ptr].enable(
              active_hor, hor_ix, int(i) - 1, my_zeroes.size() + i, knees.size());
        }
        break;
      }

      if (verbosity >= 0) printf("I %d\n", i - 1);

      // If there is no added_var before the guessed variable, set its backjumper to the
      // start of the added branch.
      if (i == 1) {
        acc_backjumpers[acc_ptr].enable(
            active_hor, hor_ix, -1, my_zeroes.size(), knees.size());
        goto total_break;
      }

      assert(x.first == lvl);
      i--;
    }
  }
total_break:

  // append added_vars to my_zeroes
  auto beg = boost::make_transform_iterator(added_vars.begin(), pair_snd);
  auto end = boost::make_transform_iterator(added_vars.end(), pair_snd);
  my_zeroes.reserve(my_zeroes.size() + added_vars.size());
  my_zeroes.insert(my_zeroes.end(), beg, end);

  S.cancelUntil(max_level);
  return CutKnee();
}


void Knee::cut() {
  vector<HorHead> &hors = *(*active_hor)[hor_ix].hors;
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
  if (hor_ix == active_hor->size()) {
    return WhatToDo::DONE;
  }

  VerHead &ver_head = (*active_hor)[hor_ix];
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
  VerHead &ver_head = (*active_hor)[hor_ix];
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
  if (hor_ix >= active_hor->size()) return true;

  unsigned out = ver_ix >= 0
    ? (*(*active_hor)[hor_ix].hors)[ver_ix].tag
    : (*active_hor)[hor_ix].tag;
  Lit out_lit = S.outputs[out];

  if (var(out_lit) != var(p)) return true;

  WhatToDo what_to_do;

  while (true) {
    if (ver_ix != -1) {
      if (S.value(out_lit) == l_True) {
        knees.emplace_back(active_hor, hor_ix, ver_ix);

        vector<VerHead> *hor = (*(*active_hor)[hor_ix].hors)[ver_ix].vers;
        if (hor == NULL) {
          move_right = true;
          what_to_do = WhatToDo::DONE;
        }
        else {
          active_hor = (*(*active_hor)[hor_ix].hors)[ver_ix].vers;
          hor_ix = 0;
          ver_ix = -1;
          what_to_do = after_hors_change(S);
        }
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
          ? (*(*active_hor)[hor_ix].hors)[ver_ix].tag
          : (*active_hor)[hor_ix].tag;
        out_lit = S.outputs[out];
        continue;
      }

      case WATCH: {
        if (verbosity >= 2) printf("WATCH %d %d\n", hor_ix, ver_ix);
        out_lit = S.outputs[ver_ix != -1
          ? (*(*active_hor)[hor_ix].hors)[ver_ix].tag
          : (*active_hor)[hor_ix].tag
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
          ? (*(*active_hor)[hor_ix].hors)[ver_ix].tag
          : (*active_hor)[hor_ix].tag
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
  if (acc_backjumpers[active_var].enabled) {
    if (verbosity >= 2) printf("ACC_UNDO_BACKJUMP\n");
    acc_backjumpers[active_var].enabled = false;
    acc_backjumpers[active_var].backjumper.jump(S);
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


bool Trie::reset(Solver &S) {
  active_hor = &root;
  hor_ix = 0;
  ver_ix = -1;
  active_var = 0;
  active_var_old = 0;
  propagations.clear();
  my_zeroes.clear();
  knees.clear();
  move_right = false;

  if (verbosity >= 2) printf("RESET\n");

  WhatToDo what_to_do = after_hors_change(S);
  unsigned out;
  Lit out_lit;

  while (true) {
    switch (what_to_do) {
      case AGAIN: {
        if (verbosity >= 2) printf("AGAIN %d %d\n", hor_ix, ver_ix);
        out = ver_ix >= 0
          ? (*(*active_hor)[hor_ix].hors)[ver_ix].tag
          : (*active_hor)[hor_ix].tag;
        out_lit = S.outputs[out];
        break;
      }

      case WATCH: {
        if (verbosity >= 2) printf("WATCH %d %d\n", hor_ix, ver_ix);
        out_lit = S.outputs[ver_ix != -1
          ? (*(*active_hor)[hor_ix].hors)[ver_ix].tag
          : (*active_hor)[hor_ix].tag
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
          ? (*(*active_hor)[hor_ix].hors)[ver_ix].tag
          : (*active_hor)[hor_ix].tag
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

    if (ver_ix != -1) {
      if (S.value(out_lit) == l_True) {
        knees.emplace_back(active_hor, hor_ix, ver_ix);

        vector<VerHead> *hor = (*(*active_hor)[hor_ix].hors)[ver_ix].vers;
        if (hor == NULL) {
          move_right = true;
          what_to_do = WhatToDo::DONE;
        }
        else {
          active_hor = (*(*active_hor)[hor_ix].hors)[ver_ix].vers;
          hor_ix = 0;
          ver_ix = -1;
          what_to_do = after_hors_change(S);
        }
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
  }
}


void PropUndo::undo(Solver &S, Lit _p) {
  S.trie->propagations.pop_back();
}


void ActiveVarDoneUndo::undo(Solver &S, Lit _p) {
  S.trie->active_var = S.trie->active_var_old;
}


void BackJumperUndo::undo(Solver &S, Lit _p) {
  S.trie->backjumpers.back().jump(S);
  S.trie->backjumpers.pop_back();
}


void BackJumper::jump(Solver &S) {
  Trie &trie = *S.trie;

  trie.move_right = false;

  trie.active_hor = active_hor;
  trie.hor_ix = hor_ix;
  trie.ver_ix = ver_ix;
  trie.my_zeroes.erase(
      trie.my_zeroes.begin() + my_zeroes_size,
      trie.my_zeroes.end()
  );
  trie.knees.erase(
      trie.knees.begin() + knees_size,
      trie.knees.end()
  );

  if (verbosity >= 2) printf("UNDO %d %d %lu\n", hor_ix, ver_ix, active_hor->size());
  Lit out_lit = S.outputs[ver_ix >= 0
    ? (*(*active_hor)[hor_ix].hors)[ver_ix].tag
    : (*active_hor)[hor_ix].tag
  ];
  trie.watch(S, var(out_lit));
  if (verbosity >= 2) printf("WU " L_LIT "\n", L_lit(out_lit));
}
