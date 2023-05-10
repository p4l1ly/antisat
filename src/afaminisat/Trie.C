#include <algorithm>
#include <iostream>
#include <fstream>
#include <utility>
#include <boost/iterator/transform_iterator.hpp>


#include "Trie.h"
#include "Solver.h"

int hor_head_count = 0;
int hor_count = 0;
int ver_count = 0;
ActiveVarDoneUndo ACTIVE_VAR_DONE_UNDO = {};
RemovedWatch REMOVED_WATCH = {};


using std::cout;

inline HorHead &Place::deref_ver() const {
  return hor->elems[hor_ix].hors[ver_ix];
}

inline VerHead &Place::deref_hor() const {
  return hor->elems[hor_ix];
}

inline unsigned Place::get_tag() const {
  return ver_ix == IX_NULL ? deref_hor().tag : deref_ver().tag;
}

inline bool Place::hor_is_out() const {
  return hor_ix == hor->elems.size();
}

inline bool Place::ver_is_singleton() const {
  return deref_hor().hors.size() == 0;
}

inline bool Place::ver_is_last() const {
  return ver_ix + 1 == deref_hor().hors.size();
}

inline bool Place::is_ver() const {
  return ver_ix != IX_NULL;
}

inline bool Place::in_conflict() const {
  return ver_ix == deref_hor().hors.size();
}

void Place::cut_away() {
  vector<HorHead> &hors = deref_hor().hors;
  if (verbosity >= 2) std::cout << "CUTTING " << *this << "\n";
  hors.erase(hors.begin() + ver_ix, hors.end());
}

inline void WatchedPlace::set_watch(Solver &S) {
  if (verbosity >= 2) {
    printf("WATCHING " L_LIT "\n", L_lit(S.outputs[get_tag()]));
  }
  int var_ = var(S.outputs[get_tag()]);
  var_ += var_;
  {
    vec<Constr*> &watches = S.watches[var_];
    watch_ix_pos = watches.size();
    watches.push(this);
  }

  var_++;
  {
    vec<Constr*> &watches = S.watches[var_];
    watch_ix_neg = watches.size();
    watches.push(this);
  }
}


void WatchedPlace::moveWatch(int i, Lit p) {
  if (sign(p)) watch_ix_neg = i;
  else watch_ix_pos = i;
}


inline void WatchedPlace::remove_watch(Solver &S, unsigned old_tag) {
  int var_ = var(S.outputs[old_tag]);
  var_ += var_;
  {
    vec<Constr*> &watches = S.watches[var_];
    if (verbosity >= 2) {
      printf("RemoveWatchPos %d %d %d\n", watches.size(), watch_ix_pos, var(S.outputs[old_tag]));
    }
    if (watches.size() == watch_ix_pos + 1) {
      watches.pop();
    } else {
      watches[watch_ix_pos] = &REMOVED_WATCH;
    }
  }

  var_++;
  {
    vec<Constr*> &watches = S.watches[var_];
    if (verbosity >= 2) {
      printf("RemoveWatchNeg %d %d %d %d\n", var_, watches.size(), watch_ix_neg, var(S.outputs[old_tag]));
    }
    if (watches.size() == watch_ix_neg + 1) {
      watches.pop();
    } else {
      watches[watch_ix_neg] = &REMOVED_WATCH;
    }
  }
}

inline void WatchedPlace::remove_watch_pos(Solver &S, Lit lit) {
  {
    vec<Constr*> &watches = S.watches[index(lit)];
    if (verbosity >= 2) {
      printf("RemoveWatchPos2 %d %d " L_LIT "\n", watches.size(), watch_ix_pos, L_lit(lit));
    }
    if (watches.size() == watch_ix_pos + 1) {
      watches.pop();
    } else {
      watches[watch_ix_pos] = &REMOVED_WATCH;
    }
  }
}

inline void WatchedPlace::remove_watch_neg(Solver &S, Lit lit) {
  {
    vec<Constr*> &watches = S.watches[index(lit)];
    if (verbosity >= 2) {
      printf("RemoveWatchNeg2 %d %d " L_LIT "\n", watches.size(), watch_ix_neg, L_lit(lit));
    }
    if (watches.size() == watch_ix_neg + 1) {
      watches.pop();
    } else {
      watches[watch_ix_neg] = &REMOVED_WATCH;
    }
  }
}

WatchedPlace::WatchedPlace(HorLine *hor_)
: Place{hor_, 0, IX_NULL}
{ }
WatchedPlace::WatchedPlace(Place place)
: Place(place)
{ }

void Trie::on_accept(Solver &S) {
  if (is_ver()) {
    ver_accept = true;
  }
  accept_level = S.decisionLevel();
}

Trie::Trie()
: WatchedPlace(&root)
, root{{NULL, 0, 0}, vector<VerHead>()}
, greater_places()
, free_greater_places()
, var_count()
, back_ptrs()
, acc_backjumpers()
, greater_backjumpers()
, greater_stack()
, to_cut{NULL}
{ }

void Trie::init(unsigned var_count_) {
  var_count = var_count_;
  back_ptrs.resize(var_count_);
  acc_backjumpers.resize(var_count_);
  greater_stack.reserve(var_count_);
}

// TODO The only undoable is Trie itself. It holds a list of undos.
Lit Trie::guess(Solver &S) {
  if (!ver_accept && !hor_is_out()) {
    unsigned tag = get_tag();
    Lit out_lit = S.outputs[tag];

    S.undos[var(out_lit)].push(&greater_backjumpers.emplace_back(*this));

    if (verbosity >= 2) {
      printf(
          "GUESS_%s %d %d %d " L_LIT "\n",
          is_ver() ? "VER" : "HOR",
          hor_ix, ver_ix, tag,
          L_lit(out_lit)
      );
    }
    return out_lit;
  }
  else if (last_greater != IX_NULL) {
    unsigned tag = greater_places[last_greater].get_tag();
    Lit out_lit = S.outputs[tag];
    S.undos[var(out_lit)].push(&greater_backjumpers.emplace_back(S.decisionLevel()));
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
    S.undos[var(S.trail.last())].push(&ACTIVE_VAR_DONE_UNDO);
    if (verbosity >= 2) printf("noguess %d\n", active_var_old);
    return lit_Undef;
  }
}

inline unsigned pair_snd(const std::pair<int, unsigned> &x) {
  return x.second;
}

void Trie::onSat(Solver &S) {
  if (verbosity >= 2) printf("ON_SAT\n");

  unordered_set<unsigned> my_zeroes_set;

  ITER_MY_ZEROES(*this, x,
      my_zeroes_set.insert(x);
  )

  // max level of added_vars+my_zeroes
  int max_level = -1;
  int last_but_max_level = -2;

  // added_vars are (level, variable) pairs, of zero variables added in the
  // accepting condition (= not included in my_zeroes)
  vector<std::pair<int, unsigned>> added_vars;
  added_vars.reserve(var_count);
  for (unsigned x = 0; x < var_count; x++) {
    if (S.value(S.outputs[x]) == l_False) {
      int lvl = S.level[var(S.outputs[x])];
      if (lvl > max_level) {
        last_but_max_level = max_level;
        max_level = lvl;
      }
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
    to_cut = ver_accept ? *this : hor->back_ptr;

    // We should get there (or further back) via backjumpers but there's an
    // edge case where there are no backjumpers (if all my_zeroes were derived
    // from the input assumptions)
    if (max_level == 0) {
      ver_accept = false;
      (Place &)*this = Place{&root, (unsigned)root.elems.size(), IX_NULL};
    }

    S.cancelUntil(max_level);
    return;
  }

  // sort added_vars by level
  std::sort(added_vars.begin(), added_vars.end());

  if (verbosity >= 2) {
    for (auto x: added_vars) {
       printf(
          "ADDED_VAR %d %d " L_LIT "\n",
          std::get<0>(x), std::get<1>(x), L_lit(S.outputs[std::get<1>(x)])
       );
     }
  }

  const std::pair<int, unsigned>& first_added_var = added_vars[0];

  HorLine *extended_hor;
  unsigned extended_hor_ix;
  if (ver_accept) {
    // We create a new horizontal empty branch right to the current final place
    // (which is vertical because least_ver_accept is set only when accepting at
    // vertical places).
    HorLine *new_active_hor = new HorLine{*this};
    if (verbosity >= -2) hor_count++;
    deref_ver().hor = new_active_hor;
    extended_hor = new_active_hor;
    extended_hor_ix = 0;
  } else {
    extended_hor = hor;
    extended_hor_ix = hor_ix;
  }

  // We need to be in an accepting state because we don't watch to anything.
  // Moreover, there's one special edge case where no backjumper and no reset
  // is called: all my_zeroes are at level 0, except the last one. In that case,
  // the conflict machinery will immediately set the last my_zero to 1 and we
  // should end up in that accepting state. We move there already here.
  if (added_vars.size() == 1) {
    ver_accept = false;
    hor = extended_hor;
    hor_ix = extended_hor_ix + 1;
    ver_ix = -1;
  } else {
    ver_accept = true;
    hor = extended_hor;
    hor_ix = extended_hor_ix;
    ver_ix = added_vars.size() - 2;
  }

  // Add the first added_var to the current horizontal branch.
  VerHead &ver_head = extended_hor->elems.emplace_back(first_added_var.second);
  ver_head.hors.reserve(added_vars.size() - 1);

  // Continue down with a vertical branch containing the remaining added_vars.
  ver_head.hors.reserve(added_vars.size() - 1);
  for (unsigned i = 1; i < added_vars.size(); i++) {
    ver_head.hors.emplace_back(added_vars[i].second);
  }

  unsigned i = added_vars.size();

  // For each greater/accepting guess, find the least place in the newly
  // created branch, that has higher or equal level as the guess. If such place
  // exists and if it is not the lowest place, set the guess' backjumper to
  // jump to the place.
  //
  // Why is the lowest place skipped? We never want to jump to the lowest place
  // because we should propagate from it immediately, which is not possible
  // from undo. Luckily, the conflict analysis machinery ensures longer jumps.
  // Are we sure? Proof: If there are multiple my_zeroes in the max_level, we
  // jump to the first of them, therefore we don't end up at the lowest one. If
  // there is only one, it is used as an asserting literal but we jump further
  // back, to the max level of the remaining literals.
  //
  // A special edge case occurs if there is nowhere further back to jump - all
  // the other my_zeroes have been added through input assumptions. In that
  // case however, the last added_var is forced to 1 via conflict analysis (it
  // is the asserting literal), there is no backjump and the trie remains
  // correctly in the ver_accept state at the last added_var.

  // We go from the lastly guessed variable to the firstly guessed one.
  // To each guessed variable, we assign a backjumper that points to the
  // last place with a level lower than the level of the guessed variable.
  //
  // Why is this so complicated? Shouldn't that always be just the added_var
  // immediately before the guessed added var? No because guessed variables are
  // of course not in added_vars, as they are 1-valued.
  for (unsigned acc_ptr = active_var_old; acc_ptr--; acc_ptr = back_ptrs[acc_ptr]) {
    int lvl = S.level[var(S.outputs[acc_ptr])];

    // How could this be even possible? If the new branch is added, the list
    // of the guessed variables does not get fully erased in the conflict
    // triggered by the new branch.
    if (lvl <= accept_level) break;

    if (verbosity >= 0) {
      printf(
        "LVL %d %d " L_LIT " %d\n",
        lvl, acc_ptr, L_lit(S.outputs[acc_ptr]), back_ptrs[acc_ptr]
      );
    }

    while (true) {
      const std::pair<int, unsigned>& added_var = added_vars[i - 1];
      if (added_var.first < lvl) {
        // We don't set the backjumper to the last added var because it will be
        // jumped over yet in onSatConflict.
        if (i + 1 < added_vars.size()) {
          acc_backjumpers[acc_ptr].enable({extended_hor, extended_hor_ix, i - 1});
        }
        break;
      }

      if (verbosity >= 0) printf("I %d\n", i - 1);

      // If there is no added_var before the guessed variable, set its backjumper to the
      // start of the added branch.
      if (i == 1) {
        if (1 != added_vars.size()) {
          acc_backjumpers[acc_ptr].enable({extended_hor, extended_hor_ix, IX_NULL});
        }
        break;
      }
      i--;
    }
  }

  for (auto it = greater_backjumpers.rbegin(); it != greater_backjumpers.rend(); it++) {
    GreaterBackjumper &backjumper = *it;
    int lvl = backjumper.level + 1;
    if (lvl <= accept_level) break;
    if (verbosity >= 0) printf("GLVL %d\n", lvl);

    while (true) {
      const std::pair<int, unsigned>& added_var = added_vars[i - 1];
      if (added_var.first < lvl) {
        // We don't set the backjumper to the last added var because it will be
        // jumped over yet in onSatConflict.
        if (i + 1 < added_vars.size()) {
          backjumper.level = -1;
          backjumper.least_backjumper = {extended_hor, extended_hor_ix, i - 1};
        }
        break;
      }

      if (verbosity >= 0) printf("I %d\n", i - 1);

      // If there is no added_var before the guessed variable, set its backjumper to the
      // start of the added branch.
      if (i == 1) {
        if (1 != added_vars.size()) {
          backjumper.level = -1;
          backjumper.least_backjumper = {extended_hor, extended_hor_ix, IX_NULL};
        }
        break;
      }
      i--;
    }
  }


  S.cancelUntil(max_level);
}


WhatToDo Place::after_hors_change(Solver &S) {
  if (hor_is_out()) return WhatToDo::DONE;

  unsigned out = get_tag();
  if (verbosity >= 2) printf("OUT %d %d\n", out, var(S.outputs[out]));
  lbool val = S.value(S.outputs[out]);

  if (val == l_Undef) {
    return ver_is_singleton() ? WhatToDo::PROPAGATE : WhatToDo::WATCH;
  }
  if (val == l_False && ver_is_singleton()) {
    ver_ix = 0;
    return WhatToDo::CONFLICT;
  }
  return WhatToDo::AGAIN;
}


WhatToDo Place::after_vers_change(Solver &S) {
  unsigned out = get_tag();
  if (verbosity >= 2) printf("OUT %d %d\n", out, var(S.outputs[out]));
  lbool val = S.value(S.outputs[out]);

  if (val == l_Undef) {
    return ver_is_last() ? WhatToDo::PROPAGATE : WhatToDo::WATCH;
  }
  if (val == l_False && ver_is_last()) {
    ++ver_ix;
    return WhatToDo::CONFLICT;
  }
  return WhatToDo::AGAIN;
}


inline GreaterPlace &add_greater_place(ChangedGreaterPlace changed_place, Trie &trie) {
  unsigned ix;
  GreaterPlace *place;

  if (trie.free_greater_places.empty()) {
    ix = trie.greater_places.size();
    place = &trie.greater_places.emplace_back(changed_place, ix, trie.last_greater);
  } else {
    ix = trie.free_greater_places.back();
    trie.free_greater_places.pop_back();
    place = &trie.greater_places[ix];
    *place = GreaterPlace(changed_place, ix, trie.last_greater);
  }

  if (trie.last_greater != IX_NULL) trie.greater_places[trie.last_greater].next = ix;
  trie.last_greater = ix;
  return *place;
}


GreaterPlace &Place::save_as_greater(Solver &S) {
  Trie &trie = S.trie;

  ChangedGreaterPlace changed_place;
  changed_place.place = *this;
  if (trie.greater_backjumpers.empty()) {
    changed_place.backjumper = NULL;
  } else {
    GreaterBackjumper &backjumper = trie.greater_backjumpers.back();
    changed_place.backjumper = &backjumper;
    changed_place.backjumper_added_ix = backjumper.added_places.size();
  }

  GreaterPlace &place = add_greater_place(changed_place, trie);
  if (changed_place.backjumper) {
    changed_place.backjumper->added_places.emplace_back(place.ix);
  }
  place.set_watch(S);
  return place;
}


void Place::branch(Solver &S) {
  if (is_ver()) {
    HorLine *hor2 = deref_ver().hor;
    if (hor2 == NULL) return;

    if (verbosity >= 2) {
      std::cout << "ADD_TO_GREATER_STACK " << PlaceAttrs(Place{hor2, 0, IX_NULL}, S) << "\n";
    }
    S.trie.greater_stack.emplace_back(hor2, 0, IX_NULL);
  } else {
    if (hor_ix + 1 == hor->elems.size()) return;
    if (verbosity >= 2) {
      std::cout << "ADD_TO_GREATER_STACK2 " << PlaceAttrs(Place{hor, hor_ix + 1, IX_NULL}, S) << "\n";
    }
    S.trie.greater_stack.emplace_back(hor, hor_ix + 1, IX_NULL);
  }
}


bool Place::handle_greater_stack(Solver &S) {
  if (verbosity >= 2) {
    std::cout << "HANDLE_GREATER_STACK " << PlaceAttrs(*this, S) << "\n";
  }
  switch (multimove_on_propagate(S, after_hors_change(S))) {
    case MultimoveEnd::E_WATCH: {
      save_as_greater(S);
      return true;
    }
    case MultimoveEnd::E_DONE: {
      return true;
    }
    case MultimoveEnd::E_PROPAGATE: {
      return S.enqueue(S.outputs[get_tag()], &save_as_greater(S));
    }
    default: { // case MultimoveEnd::E_CONFLICT:
      return false;
    }
  }
}


WhatToDo Place::move_on_propagate(Solver &S, Lit out_lit) {
  if (is_ver()) {
    if (S.value(out_lit) == l_True) {
      HorLine *hor2 = deref_ver().hor;
      if (hor2 == NULL) return WhatToDo::DONE;
      else {
        hor = hor2;
        hor_ix = 0;
        ver_ix = IX_NULL;
        return after_hors_change(S);
      }
    }
    else {
      branch(S);
      ver_ix++;
      return after_vers_change(S);
    }
  }
  else {
    if (S.value(out_lit) == l_True) {
      hor_ix++;
      return after_hors_change(S);
    }
    else {
      branch(S);
      ver_ix++;
      return after_vers_change(S);
    }
  }
}


MultimoveEnd Place::multimove_on_propagate(Solver &S, WhatToDo what_to_do) {
  unsigned out;
  Lit out_lit;

  while (true) {
    switch (what_to_do) {
      case AGAIN: {
        if (verbosity >= 2) {
          printf("AGAIN %d %d %d\n", hor_ix, ver_ix, var(S.outputs[get_tag()]));
        }
        out = get_tag();
        out_lit = S.outputs[out];
        break;
      }

      case WATCH: {
        if (verbosity >= 2) {
          printf("WATCH %d %d " L_LIT "\n", hor_ix, ver_ix, L_lit(S.outputs[get_tag()]));
        }
        return MultimoveEnd::E_WATCH;
      }

      case DONE: {
        if (verbosity >= 2) {
          printf("DONE %d %d\n", hor_ix, ver_ix);
        }
        return MultimoveEnd::E_DONE;
      }

      case PROPAGATE: {
        if (verbosity >= 2) {
          printf("PROPAGATE %d %d " L_LIT "\n", hor_ix, ver_ix, L_lit(S.outputs[get_tag()]));
        }

        return MultimoveEnd::E_PROPAGATE;
      }

      case CONFLICT: {
        if (verbosity >= 2) {
          printf("CONFLICT %d %d\n", hor_ix, ver_ix);
        }
        return MultimoveEnd::E_CONFLICT;
      }
    }

    what_to_do = move_on_propagate(S, out_lit);
  }
}

bool WatchedPlace::full_multimove_on_propagate(Solver &S, WhatToDo what_to_do) {
  MultimoveEnd end = multimove_on_propagate(S, what_to_do);
  if (end == MultimoveEnd::E_CONFLICT) {
    S.trie.greater_stack.clear();
    return false;
  } else {
    while (!S.trie.greater_stack.empty()) {
      Place p = S.trie.greater_stack.back();
      S.trie.greater_stack.pop_back();
      if (!p.handle_greater_stack(S)) {
        S.trie.greater_stack.clear();
        return false;
      }
    }
  }

  switch (end) {
    case MultimoveEnd::E_WATCH: {
      set_watch(S);
      return true;
    }
    case MultimoveEnd::E_DONE: {
      on_accept(S);
      return true;
    }
    case MultimoveEnd::E_PROPAGATE: {
      set_watch(S);
      return S.enqueue(S.outputs[get_tag()], this);
    }
    default: { // case MultimoveEnd::E_CONFLICT:
      return false;
    }
  }
}

bool WatchedPlace::propagate(Solver& S, Lit p, bool& keep_watch) {
  if (verbosity >= 2) {
    printf("PROP %d %d " L_LIT "\n", hor_ix, ver_ix, L_lit(p));
  }
  if (sign(p)) {
    remove_watch_pos(S, ~p);
  } else {
    remove_watch_neg(S, ~p);
  }
  return full_multimove_on_propagate(S, move_on_propagate(S, S.outputs[get_tag()]));
}


void Trie::undo(Solver& S, Lit p) {
  active_var--;
  if (acc_backjumpers[active_var].enabled) {
    if (verbosity >= 2) printf("ACC_UNDO_BACKJUMP\n");
    acc_backjumpers[active_var].enabled = false;
    acc_backjumpers[active_var].jump(S);
  }

  active_var = back_ptrs[active_var];
  if (verbosity >= 2) printf("ACC_UNDO %d " L_LIT "\n", active_var, L_lit(p));
}


void WatchedPlace::calcReason(Solver& S, Lit p, vec<Lit>& out_reason) {
  if (p == lit_Undef) {
    int max_level = -1;
    ITER_MY_ZEROES(*this, x,
      Lit out_lit = S.outputs[x];
      max_level = max(max_level, S.level[var(out_lit)]);
      out_reason.push(~out_lit);
    )

    if (verbosity >= 2) {
      printf("CALC_REASON_CONFLICT " L_LIT, L_lit(p));
      ITER_MY_ZEROES(*this, x, printf(" %u", x);)
      printf("\n");
    }

    S.cancelUntil(max_level);
  }
  else {
    ITER_MY_ZEROES(*this, x, out_reason.push(~S.outputs[x]);)

    if (verbosity >= 2) {
      printf("CALC_REASON_PLACE " L_LIT, L_lit(p));
      ITER_MY_ZEROES(*this, x, printf(" %u", x);)
      printf("\n");
    }
  }
}


bool Trie::reset(Solver &S) {
  if (!ver_accept && !hor_is_out() && !in_conflict()) {
    remove_watch(S, get_tag());
  }

  {
    int greater_ix = last_greater;
    while (true) {
      if (greater_ix == IX_NULL) break;
      if (verbosity >= 2) printf("ResettingGreater %d\n", greater_ix);
      GreaterPlace &place = greater_places[greater_ix];
      if (!place.in_conflict()) {
        place.remove_watch(S, place.get_tag());
      }
      greater_ix = place.previous;
    }
  }
  greater_places.clear();
  free_greater_places.clear();
  last_greater = IX_NULL;

  hor = &root;
  hor_ix = 0;
  ver_ix = IX_NULL;

  active_var = 0;
  active_var_old = 0;
  ver_accept = false;

  if (verbosity >= 2) printf("RESET\n");

  bool result = full_multimove_on_propagate(S, after_hors_change(S));
  if (to_cut.hor != NULL) {
    to_cut.cut_away();
    to_cut.hor = NULL;
  }

  return result;
}


void ActiveVarDoneUndo::undo(Solver &S, Lit _p) {
  S.trie.active_var = S.trie.active_var_old;
}


void BackJumper::jump(Solver &S) {
  Trie &trie = S.trie;

  if (!trie.ver_accept && !trie.hor_is_out() && !trie.in_conflict()) {
    trie.remove_watch(S, trie.get_tag());
  }
  (Place&)trie = place;
  trie.ver_accept = false;

  if (verbosity >= 2) {
    printf("UNDO %d %d %lu\n", place.hor_ix, place.ver_ix, place.hor->elems.size());
  }
  Lit out_lit = S.outputs[place.get_tag()];
  trie.set_watch(S);
  if (verbosity >= 2) printf("WU " L_LIT "\n", L_lit(out_lit));
}


GreaterPlace::GreaterPlace(HorLine *hor_, unsigned ix_, unsigned previous_)
: WatchedPlace(hor_), ix(ix_), backjumper(NULL), previous(previous_), next(IX_NULL)
{ }

GreaterPlace::GreaterPlace(
  ChangedGreaterPlace changed_place, unsigned ix_, unsigned previous_
)
: WatchedPlace(changed_place.place)
, ix(ix_)
, backjumper(changed_place.backjumper)
, backjumper_added_ix(changed_place.backjumper_added_ix)
, previous(previous_)
, next(IX_NULL)
{ }


void GreaterPlace::on_accept(Solver &S) {
  enabled = false;

  Trie &trie = S.trie;

  if (previous != IX_NULL) trie.greater_places[previous].next = next;
  if (next == IX_NULL) trie.last_greater = previous;
  else trie.greater_places[next].previous = previous;

  if (trie.greater_places.size() == ix + 1) {
    trie.greater_places.pop_back();
  } else {
    trie.free_greater_places.emplace_back(ix);
  }

  if (!trie.greater_backjumpers.empty()) {
    GreaterBackjumper &last_backjumper = trie.greater_backjumpers.back();
    if (&last_backjumper == backjumper) {
      last_backjumper.added_places[backjumper_added_ix].removed = true;
    } else if (is_ver()) {
      last_backjumper.changed_places.emplace_back(*this, backjumper, backjumper_added_ix);
    } else {
      last_backjumper.changed_places.emplace_back(
        Place{hor, hor_ix - 1, IX_NULL}, backjumper, backjumper_added_ix
      );
    }
  }
}


void GreaterBackjumper::undo(Solver &S, Lit _p) {
  Trie &trie = S.trie;

  if (level == -1) {
    least_backjumper.jump(S);
  }

  for (AddedGreaterPlace added_place: added_places) {
    if (added_place.removed) continue;
    const unsigned ix = added_place.ix;
    GreaterPlace &place = trie.greater_places[added_place.ix];
    if (!place.in_conflict()) {
      place.remove_watch(S, place.get_tag());
    }

    if (place.previous != IX_NULL) trie.greater_places[place.previous].next = place.next;
    if (place.next == IX_NULL) trie.last_greater = place.previous;
    else trie.greater_places[place.next].previous = place.previous;

    if (trie.greater_places.size() == added_place.ix + 1) {
      trie.greater_places.pop_back();
    } else {
      trie.greater_places[added_place.ix].enabled = false;
      trie.free_greater_places.push_back(added_place.ix);
    }
  }

  for (ChangedGreaterPlace changed_place: changed_places) {
    GreaterPlace &place = add_greater_place(changed_place, trie);
    if (changed_place.backjumper) {
      changed_place.backjumper->added_places[changed_place.backjumper_added_ix].ix = place.ix;
    }
    if (verbosity >= 2) std::cout << "CHANGED " << place << "\n" << std::flush;
    place.set_watch(S);
  }

  trie.greater_backjumpers.pop_back();
}


void Trie::to_dot(Solver& S, const char *filename) {
  std::ofstream file;
  file.open(filename);
  file << "strict graph {\n";

  vector<HorLine*> stack;
  stack.push_back(&root);

  while (!stack.empty()) {
    HorLine* hor = stack.back();
    stack.pop_back();

    // Pose the line horizontally.
    file << "subgraph { rank=same";
    if (hor->back_ptr.hor != NULL) {
      file << ";" << hor->back_ptr;
    }
    for (Place p = {hor, 0, IX_NULL}; p.hor_ix < hor->elems.size(); p.hor_ix++) {
      file << ";" << p;
    }
    file << " };\n";

    // Connect the horizontal line and make it infinitely flexible.
    if (hor->back_ptr.hor != NULL) {
      Place p = hor->back_ptr;
      Place p2 = {hor, 0, IX_NULL};
      file << p2 << " " << PlaceAttrs(p2, S) << "\n";
      file << p << " -- " << p2 << " [constraint=false];\n";
    } else if (!hor->elems.empty()) {
      Place p2 = {hor, 0, IX_NULL};
      file << p2 << " " << PlaceAttrs(p2, S) << "\n";
    }
    for (Place p = {hor, 0, IX_NULL}; p.hor_ix + 1 < hor->elems.size(); p.hor_ix++) {
      Place p2 = p;
      p2.hor_ix++;
      file << p2 << " " << PlaceAttrs(p2, S) << "\n";
      file << p << " -- " << p2 << " [constraint=false];\n";
    }

    // Draw the vertical lines and recur into branching horizontal lines.
    for (unsigned hor_ix = 0; hor_ix < hor->elems.size(); hor_ix++) {
      Place p1 = {hor, hor_ix, IX_NULL};
      for (Place p2 = {hor, hor_ix, 0}; p2.ver_ix < p2.deref_hor().hors.size(); p2.ver_ix++) {
        file << p2 << " " << PlaceAttrs(p2, S) << "\n";
        file << p1 << " -- " << p2 << ";\n";
        HorLine *hor2 = p2.deref_ver().hor;
        if (hor2 != NULL) {
          stack.push_back(hor2);
        }
        p1 = p2;
      }
    }
  }

  file << "}\n";
  file.close();
}

std::ostream& operator<<(std::ostream& os, Place const &p) {
  return os << '"' << p.hor << ',' << p.hor_ix << ',' << p.ver_ix << '"';
}

std::ostream& operator<<(std::ostream& os, PlaceAttrs const &p) {
  return
    os << "["
    << "label=\"" << var(p.S.outputs[p.get_tag()]) << "\","
    << "tooltip=" << (Place&)p
    << "]";
}
