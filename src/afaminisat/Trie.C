#include <algorithm>
#include <iostream>
#include <utility>
#include <boost/iterator/transform_iterator.hpp>


#include "Trie.h"
#include "Solver.h"

int hor_head_count = 0;
int hor_count = 0;
int ver_count = 0;
ActiveVarDoneUndo ACTIVE_VAR_DONE_UNDO = {};
BackJumperUndo BACKJUMPER_UNDO = {};
RemovedWatch REMOVED_WATCH = {};

using std::cout;

inline HorHead &Place::deref_ver() {
  return hor->elems[hor_ix].hors[ver_ix];
}

inline VerHead &Place::deref_hor() {
  return hor->elems[hor_ix];
}

inline unsigned Place::get_tag() {
  return ver_ix == -1 ? deref_hor().tag : deref_ver().tag;
}

inline bool Place::hor_is_out() {
  return hor_ix == hor->elems.size();
}

inline bool Place::ver_is_singleton() {
  return deref_hor().hors.size() == 0;
}

inline bool Place::ver_is_last() {
  return ver_ix + 1 == deref_hor().hors.size();
}

inline bool Place::is_ver() {
  return ver_ix != -1;
}

void Place::cut_away() {
  vector<HorHead> &hors = deref_hor().hors;
  if (verbosity >= 2) printf("CUTTING [%d] AT %d\n", hor_ix, ver_ix);
  hors.erase(hors.begin() + ver_ix, hors.end());
}

inline void WatchedPlace::set_watch(Solver &S) {
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

inline void WatchedPlace::remove_watch(Solver &S, unsigned old_tag) {
  int var_ = var(S.outputs[old_tag]);
  var_ += var_;
  {
    vec<Constr*> &watches = S.watches[var_];
    if (watches.size() == watch_ix_pos + 1) {
      watches.pop();
    } else {
      watches[watch_ix_pos] = &REMOVED_WATCH;
    }
  }

  var_++;
  {
    vec<Constr*> &watches = S.watches[var_];
    if (watches.size() == watch_ix_pos + 1) {
      watches.pop();
    } else {
      watches[watch_ix_neg] = &REMOVED_WATCH;
    }
  }
}

inline void WatchedPlace::update_watch(Solver &S, unsigned old_tag) {
  remove_watch(S, old_tag);
  set_watch(S);
}

WatchedPlace::WatchedPlace(HorLine *hor_)
: Place{hor_, 0, -1}
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

Trie::Trie() : WatchedPlace(&root) {};

Trie::Trie(unsigned var_count_)
: WatchedPlace(&root)
, root()
, greater_places()
, free_greater_places()
, var_count(var_count_)
, back_ptrs(var_count_)
, acc_backjumpers(var_count_)
, backjumpers()
, greater_backjumpers()
, greater_stack()
{
  backjumpers.reserve(var_count_);
  greater_backjumpers.reserve(var_count_);
  greater_stack.reserve(var_count_);
}

Lit Trie::guess(Solver &S) {
  if (!ver_accept && !hor_is_out()) {
    unsigned tag = get_tag();
    Lit out_lit = S.outputs[tag];

    backjumpers.emplace_back(*this);
    greater_backjumpers.emplace_back();
    S.undos[var(out_lit)].push(&BACKJUMPER_UNDO);

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
  // TODO guess by greater_places
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

bool Trie::onSat(Solver &S) {
  if (verbosity >= 2) printf("ON_SAT\n");

  unordered_set<unsigned> my_zeroes_set;

  ITER_MY_ZEROES(*this, x,
      my_zeroes_set.insert(x);
  )

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
    Place result = hor->back_ptr;
    S.cancelUntil(max_level);
    return true;
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

  const std::pair<int, unsigned>& x = added_vars[0];

  HorLine *hor;
  unsigned hor_ix;
  if (ver_accept) {
    // We create a new horizontal empty branch right to the current final place
    // (which is vertical because least_ver_accept is set only when accepting at
    // vertical places).
    ver_accept = false;
    HorLine *new_active_hor = new HorLine{*this};
    if (verbosity >= -2) hor_count++;
    deref_ver().hor = new_active_hor;
    hor = new_active_hor;
    hor_ix = 0;
  } else {
    hor = hor;
    hor_ix = hor_ix;
  }

  // Add the first added_var to the current horizontal branch.
  VerHead &ver_head = hor->elems.emplace_back(x.second);
  ver_head.hors.reserve(added_vars.size() - 1);

  // Continue down with a vertical branch containing the remaining added_vars.
  ver_head.hors.reserve(added_vars.size() - 1);
  for (unsigned i = 1; i < added_vars.size(); i++) {
    ver_head.hors.emplace_back(added_vars[i].second);
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
    if (lvl <= accept_level) break;

    if (verbosity >= 0) {
      printf(
        "LVL %d %d " L_LIT " %d\n",
        lvl, acc_ptr, L_lit(S.outputs[acc_ptr]), back_ptrs[acc_ptr]
      );
    }

    while (true) {
      const std::pair<int, unsigned>& x = added_vars[i - 1];
      if (x.first < lvl) {
        if (i != added_vars.size()) {
          acc_backjumpers[acc_ptr].enable(
            {hor, hor_ix, int(i) - 1}
          );
        }
        break;
      }

      if (verbosity >= 0) printf("I %d\n", i - 1);

      // If there is no added_var before the guessed variable, set its backjumper to the
      // start of the added branch.
      if (i == 1) {
        acc_backjumpers[acc_ptr].enable({hor, hor_ix, -1});
        goto total_break;
      }

      assert(x.first == lvl);
      i--;
    }
  }
  total_break:

  S.cancelUntil(max_level);
  return false;
}


WhatToDo Place::after_hors_change(Solver &S) {
  if (hor_is_out()) return WhatToDo::DONE;

  unsigned out = get_tag();
  if (verbosity >= 2) printf("OUT %d\n", out);
  lbool val = S.value(S.outputs[out]);

  if (val == l_Undef) {
    return ver_is_singleton() ? WhatToDo::PROPAGATE : WhatToDo::WATCH;
  }
  if (val == l_False && ver_is_singleton()) {
    return WhatToDo::CONFLICT;
  }
  return WhatToDo::AGAIN;
}


WhatToDo Place::after_vers_change(Solver &S) {
  unsigned out = get_tag();
  if (verbosity >= 2) printf("OUT %d\n", out);
  lbool val = S.value(S.outputs[out]);

  if (val == l_Undef) {
    return ver_is_last() ? WhatToDo::PROPAGATE : WhatToDo::WATCH;
  }
  if (val == l_False && ver_is_last()) {
    return WhatToDo::CONFLICT;
  }
  return WhatToDo::AGAIN;
}


inline GreaterPlace &add_greater_place(ChangedGreaterPlace changed_place, Trie &trie) {
  while (!trie.free_greater_places.empty()) {
    unsigned ix = trie.free_greater_places.back();
    trie.free_greater_places.pop_back();
    if (ix < trie.greater_places.size()) {
      GreaterPlace &place = trie.greater_places[ix];
      place = GreaterPlace(changed_place, ix);
      return place;
    }
  }
  unsigned ix = trie.greater_places.size();
  return trie.greater_places.emplace_back(changed_place, ix);
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
  Place place; 

  if (is_ver()) {
    HorLine *hor2 = deref_ver().hor;
    if (hor2 == NULL) return;
    place = {hor2, 0, -1};
    S.trie.greater_stack.emplace_back(hor2, 0, -1);
  } else {
    place = {hor, hor_ix + 1, -1};
    S.trie.greater_stack.emplace_back(hor, hor_ix + 1, -1);
  }
}


bool Place::handle_greater_stack(Solver &S) {
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
    case MultimoveEnd::E_CONFLICT: {
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
        ver_ix = -1;
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
          printf("AGAIN %d %d\n", hor_ix, ver_ix);
        }
        out = get_tag();
        out_lit = S.outputs[out];
        break;
      }

      case WATCH: {
        if (verbosity >= 2) {
          printf("WATCH %d %d\n", hor_ix, ver_ix);
        }
        if (verbosity >= 2) printf("WW " L_LIT "\n", L_lit(S.outputs[get_tag()]));
        return MultimoveEnd::E_WATCH;
      }

      case DONE: {
        if (verbosity >= 2) {
          printf("DONE %d %d", hor_ix, ver_ix);
        }
        return MultimoveEnd::E_DONE;
      }

      case PROPAGATE: {
        if (verbosity >= 2) {
          printf("PROPAGATE %d %d\n", hor_ix, ver_ix);
        }
        if (verbosity >= 2) printf("WP " L_LIT "\n", L_lit(S.outputs[get_tag()]));

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
      if (!p.handle_greater_stack(S)) {
        S.trie.greater_stack.clear();
        return false;
      }
      S.trie.greater_stack.pop_back();
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
    case MultimoveEnd::E_CONFLICT: {
      return false;
    }
  }
}

bool WatchedPlace::propagate(Solver& S, Lit p, bool& keep_watch) {
  if (verbosity >= 2) {
    printf("LEAST_PROP %d %d " L_LIT "\n", hor_ix, ver_ix, L_lit(p));
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
    ITER_MY_ZEROES((Place{hor, hor_ix, ver_ix + 1}), x,
      Lit out_lit = S.outputs[x];
      max_level = max(max_level, S.level[var(out_lit)]);
      out_reason.push(~out_lit);
    )

    if (verbosity >= 2) {
      printf("CALC_REASON_CONFLICT.LEAST " L_LIT, L_lit(p));
      ITER_MY_ZEROES(*this, x, printf(" %u", x);)
      printf("\n");
    }

    S.cancelUntil(max_level);
  }
  else {
    ITER_MY_ZEROES(*this, x, out_reason.push(~S.outputs[x]);)

    if (verbosity >= 2) {
      printf("CALC_REASON_PLACE.LEAST " L_LIT, L_lit(p));
      ITER_MY_ZEROES(*this, x, printf(" %u", x);)
      printf("\n");
    }
  }
}


bool Trie::reset(Solver &S) {
  if (!ver_accept && !hor_is_out()) {
    remove_watch(S, get_tag());
  }
  hor = &root;
  hor_ix = 0;
  ver_ix = -1;

  active_var = 0;
  active_var_old = 0;
  ver_accept = false;

  if (verbosity >= 2) printf("RESET\n");

  return full_multimove_on_propagate(S, after_hors_change(S));
}


void ActiveVarDoneUndo::undo(Solver &S, Lit _p) {
  S.trie.active_var = S.trie.active_var_old;
}


void BackJumperUndo::undo(Solver &S, Lit _p) {
  S.trie.backjumpers.back().jump(S);
  S.trie.backjumpers.pop_back();
}


void BackJumper::jump(Solver &S) {
  Trie &trie = S.trie;

  if (!trie.ver_accept && !trie.hor_is_out()) {
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


GreaterPlace::GreaterPlace(HorLine *hor_, unsigned ix_)
: WatchedPlace(hor_), ix(ix_), backjumper(NULL)
{ }

GreaterPlace::GreaterPlace(ChangedGreaterPlace changed_place, unsigned ix_)
: WatchedPlace(changed_place.place)
, ix(ix_)
, backjumper(changed_place.backjumper)
, backjumper_added_ix(changed_place.backjumper_added_ix)
{ }


void GreaterPlace::on_accept(Solver &S) {
  enabled = false;
  Trie &trie = S.trie;
  if (trie.greater_places.size() == ix + 1) {
    trie.greater_places.pop_back();
  } else {
    trie.free_greater_places.emplace_back(ix);
  }

  if (!trie.greater_backjumpers.empty()) {
    GreaterBackjumper &last_backjumper = trie.greater_backjumpers.back();
    if (&last_backjumper == backjumper) {
      last_backjumper.added_places[backjumper_added_ix].removed = true;
    } else {
      last_backjumper.changed_places.emplace_back(*this, backjumper, backjumper_added_ix);
    }
  }
}

void GreaterBackjumper::undo(Solver &S, Lit _p) {
  Trie &trie = S.trie;
  for (AddedGreaterPlace added_place: added_places) {
    if (added_place.removed) continue;
    const unsigned ix = added_place.ix;
    GreaterPlace &place = trie.greater_places[added_place.ix];
    place.remove_watch(S, place.get_tag());

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
    place.set_watch(S);
  }

  trie.greater_backjumpers.pop_back();
}
