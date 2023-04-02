#include <algorithm>
#include <iostream>
#include <utility>
#include <boost/iterator/transform_iterator.hpp>


#include "Trie.h"

int hor_head_count = 0;
int hor_count = 0;
int ver_count = 0;
PropUndo PROP_UNDO = {};
ActiveVarDoneUndo ACTIVE_VAR_DONE_UNDO = {};
BackJumperUndo BACKJUMPER_UNDO = {};

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

inline const char *Place::get_label() {
  return is_ver() ? "VER" : "HOR";
}

void Place::cut_away() {
  vector<HorHead> &hors = deref_hor().hors;
  if (verbosity >= 2) printf("CUTTING [%d] AT %d\n", hor_ix, ver_ix);
  hors.erase(hors.begin() + ver_ix, hors.end());
}

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
, least_place({&root, 0, -1})
, var_count(var_count_)
, back_ptrs(var_count_)
, propagations()
, acc_backjumpers(var_count_)
, watch_mask(index_count)
, backjumpers()
{
  propagations.reserve(var_count_);
  backjumpers.reserve(var_count_);
}

Lit Trie::guess(Solver &S) {
  if (!least_ver_accept && !least_place.hor_is_out()) {
    unsigned tag = least_place.get_tag();
    Lit out_lit = S.outputs[tag];

    backjumpers.emplace_back(least_place);
    S.undos[var(out_lit)].push(&BACKJUMPER_UNDO);

    if (verbosity >= 2) {
      printf(
          "GUESS_%s %d %d %d " L_LIT "\n",
          least_place.get_label(), least_place.hor_ix, least_place.ver_ix, tag,
          L_lit(out_lit)
      );
    }
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

bool Trie::onSat(Solver &S) {
  if (verbosity >= 2) printf("ON_SAT\n");

  unordered_set<unsigned> my_zeroes_set;

  ITER_MY_ZEROES(least_place, x,
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
    Place result = least_place.hor->back_ptr;
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

  if (least_ver_accept) {
    // We create a new horizontal empty branch right to the current final place
    // (which is vertical because least_ver_accept is set only when accepting at
    // vertical places).
    least_ver_accept = false;
    HorLine *new_active_hor = new HorLine{least_place};
    if (verbosity >= -2) hor_count++;
    least_place.deref_ver().hor = new_active_hor;
    least_place = {new_active_hor, 0, -1};
  }

  // Add the first added_var to the current horizontal branch.
  VerHead &ver_head = least_place.hor->elems.emplace_back(x.second);
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
    if (lvl <= last_state_level) break;

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
            {least_place.hor, least_place.hor_ix, int(i) - 1}
          );
        }
        break;
      }

      if (verbosity >= 0) printf("I %d\n", i - 1);

      // If there is no added_var before the guessed variable, set its backjumper to the
      // start of the added branch.
      if (i == 1) {
        acc_backjumpers[acc_ptr].enable({least_place.hor, least_place.hor_ix, -1});
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



void Trie::remove(Solver& S, bool just_dealloc) {
  std::cerr << "SubsetQ removed!\n";
}


bool Trie::simplify(Solver& S) {
  return false;
}


WhatToDo Trie::after_hors_change(Solver &S) {
  if (least_place.hor_is_out()) {
    return WhatToDo::DONE;
  }

  unsigned out = least_place.get_tag();
  if (verbosity >= 2) printf("OUT %d\n", out);
  lbool val = S.value(S.outputs[out]);

  if (val == l_Undef) {
    return least_place.ver_is_singleton() ? WhatToDo::PROPAGATE : WhatToDo::WATCH;
  }
  if (val == l_False && least_place.ver_is_singleton()) {
    return WhatToDo::CONFLICT;
  }
  return WhatToDo::AGAIN;
}


WhatToDo Trie::after_vers_change(Solver &S) {
  unsigned out = least_place.get_tag();
  if (verbosity >= 2) printf("OUT %d\n", out);
  lbool val = S.value(S.outputs[out]);

  if (val == l_Undef) {
    return least_place.ver_is_last() ? WhatToDo::PROPAGATE : WhatToDo::WATCH;
  }
  if (val == l_False && least_place.ver_is_last()) {
    return WhatToDo::CONFLICT;
  }
  return WhatToDo::AGAIN;
}


WhatToDo Trie::move_on_propagate(Solver &S, Lit out_lit) {
  if (least_place.is_ver()) {
    if (S.value(out_lit) == l_True) {
      HorLine *hor = least_place.deref_ver().hor;
      if (hor == NULL) {
        least_ver_accept = true;
        return WhatToDo::DONE;
      }
      else {
        least_place = {hor, 0, -1};
        return after_hors_change(S);
      }
    }
    else {
      least_place.ver_ix++;
      return after_vers_change(S);
    }
  }
  else {
    if (S.value(out_lit) == l_True) {
      least_place.hor_ix++;
      return after_hors_change(S);
    }
    else {
      least_place.ver_ix++;
      return after_vers_change(S);
    }
  }
}

bool Trie::multi_move_on_propagate(Solver &S, WhatToDo what_to_do) {
  unsigned out;
  Lit out_lit;

  while (true) {
    switch (what_to_do) {
      case AGAIN: {
        if (verbosity >= 2) {
          printf("AGAIN %d %d\n", least_place.hor_ix, least_place.ver_ix);
        }
        out = least_place.get_tag();
        out_lit = S.outputs[out];
        break;
      }

      case WATCH: {
        if (verbosity >= 2) {
          printf("WATCH %d %d\n", least_place.hor_ix, least_place.ver_ix);
        }
        out_lit = S.outputs[least_place.get_tag()];
        watch(S, var(out_lit));
        if (verbosity >= 2) printf("WW " L_LIT "\n", L_lit(out_lit));
        return true;
      }

      case DONE: {
        if (verbosity >= 2) {
          printf(
            "DONE %d %d, active_var: %d\n",
            least_place.hor_ix, least_place.ver_ix, active_var
          );
        }
        last_state_level = S.decisionLevel();
        return true;
      }

      case PROPAGATE: {
        if (verbosity >= 2) {
          printf("PROPAGATE %d %d\n", least_place.hor_ix, least_place.ver_ix);
        }
        out_lit = S.outputs[least_place.get_tag()];

        watch(S, var(out_lit));
        if (verbosity >= 2) printf("WP " L_LIT "\n", L_lit(out_lit));

        propagations.push_back(least_place);
        S.undos[var(out_lit)].push(&PROP_UNDO);
        return S.enqueue(out_lit, this);
      }

      case CONFLICT: {
          if (verbosity >= 2) {
            printf("CONFLICT %d %d\n", least_place.hor_ix, least_place.ver_ix);
          }
          return false;
      }
    }

    what_to_do = move_on_propagate(S, out_lit);
  }
}


bool Trie::propagate(Solver& S, Lit p, bool& keep_watch) {
  if (verbosity >= 2) {
    printf("PROP %d %d " L_LIT "\n", least_place.hor_ix, least_place.ver_ix, L_lit(p));
  }

  watch_mask[index(p)] = false;
  if (least_place.hor_is_out()) return true;

  unsigned out = least_place.get_tag();
  Lit out_lit = S.outputs[out];

  if (var(out_lit) != var(p)) return true;

  return multi_move_on_propagate(S, move_on_propagate(S, out_lit));
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


void Trie::calcReason(Solver& S, Lit p, vec<Lit>& out_reason) {
  if (p == lit_Undef) {
    int max_level = -1;
    ITER_MY_ZEROES(least_place, x,
      Lit out_lit = S.outputs[x];
      max_level = max(max_level, S.level[var(out_lit)]);
      out_reason.push(~out_lit);
    )

    if (verbosity >= 2) {
      printf("CALC_REASON_CONFLICT " L_LIT, L_lit(p));
      ITER_MY_ZEROES(least_place, x, printf(" %u", x);)
      printf("\n");
    }

    S.cancelUntil(max_level);
  }
  else {
    if (verbosity >= 2) printf("PROPS %lu\n", propagations.size());
    Place place = propagations.back();

    ITER_MY_ZEROES(place, x, out_reason.push(~S.outputs[x]);)

    if (verbosity >= 2) {
      printf("CALC_REASON_PLACE " L_LIT, L_lit(p));
      ITER_MY_ZEROES(place, x, printf(" %u", x);)
      printf("\n");
    }
  }
}


bool Trie::reset(Solver &S) {
  least_place = {&root, 0, -1};
  active_var = 0;
  active_var_old = 0;
  propagations.clear();
  least_ver_accept = false;

  if (verbosity >= 2) printf("RESET\n");

  return multi_move_on_propagate(S, after_hors_change(S));
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

  trie.least_ver_accept = false;
  trie.least_place = place;

  if (verbosity >= 2) {
    printf("UNDO %d %d %lu\n", place.hor_ix, place.ver_ix, place.hor->elems.size());
  }
  Lit out_lit = S.outputs[place.get_tag()];
  trie.watch(S, var(out_lit));
  if (verbosity >= 2) printf("WU " L_LIT "\n", L_lit(out_lit));
}
