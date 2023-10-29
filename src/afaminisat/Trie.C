#include <algorithm>
#include <iostream>
#include <fstream>
#include <utility>

#include "Trie.h"
#include "Solver.h"

int hor_head_count = 0;
int hor_count = 0;
int ver_count = 0;
RemovedWatch REMOVED_WATCH = {};
Mode TRIE_MODE = branch_on_zero;

inline void check(bool expr) { assert(expr); }

inline HorHead &Place::deref_ver() const {
  return hor->elems[hor_ix].hors[ver_ix];
}

inline VerHead &Place::deref_hor() const {
  return hor->elems[hor_ix];
}

inline Lit Place::get_tag() const {
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
  return !hor_is_out() && ver_ix == deref_hor().hors.size();
}

void Place::cut_away() {
  vector<HorHead> &hors = deref_hor().hors;
  if (verbosity >= 2) std::cout << "CUTTING " << *this << "\n";
  hors.erase(hors.begin() + ver_ix, hors.end());
}

inline void WatchedPlace::accept_notify_horhead(Solver& S) {
  if (is_ver()) {
    HorHead &horhead = deref_ver();
    horhead.accept_ix = my_greater_ix();
    horhead.accept_level = S.decisionLevel();
    if (verbosity >= 2) { std::cout << "FIRST_ACCEPT1" << std::endl; }
  } else {
    Place back = hor->back_ptr;
    if (back.hor == NULL) {
      Trie &trie = S.trie;
      trie.root_accept_ix = my_greater_ix();
      trie.root_accept_level = S.decisionLevel();
      if (verbosity >= 2) { std::cout << "FIRST_ACCEPT2" << std::endl; }
    } else {
      HorHead &horhead = back.deref_ver();
      horhead.accept_ix = my_greater_ix();
      horhead.accept_level = S.decisionLevel();
      if (verbosity >= 2) { std::cout << "FIRST_ACCEPT3" << std::endl; }
    }
  }
}

inline void WatchedPlace::set_watch(Solver &S) {
  if (verbosity >= 2) {
    printf("WATCHING " L_LIT "\n", L_lit(get_tag()));
  }
  int var_ = var(get_tag());
  var_ += var_;
  {
    vec<Constr*> &watches = S.watches[var_];
    watch_ix_pos = watches.size();
    if (verbosity >= 2) printf("WATCH_IX_POS %d %d\n", watch_ix_pos, var_ / 2);
    watches.push(this);
  }

  var_++;
  {
    vec<Constr*> &watches = S.watches[var_];
    watch_ix_neg = watches.size();
    if (verbosity >= 2) printf("WATCH_IX_NEG %d %d\n", watch_ix_neg, var_ / 2);
    watches.push(this);
  }
}


void WatchedPlace::moveWatch(int i, Lit p) {
  if (sign(p)) watch_ix_neg = i;
  else watch_ix_pos = i;
}


inline void WatchedPlace::remove_watch(Solver &S, Lit old_tag) {
  int var_ = var(old_tag);
  var_ += var_;
  {
    vec<Constr*> &watches = S.watches[var_];
    if (verbosity >= 2) {
      printf("RemoveWatchPos %d %d %d\n", watches.size(), watch_ix_pos, var(old_tag));
    }
#ifdef MY_DEBUG
    std::cout << std::flush; assert(watch_ix_pos >= 0);
#endif
    if (watches.size() == watch_ix_pos + 1) {
      watches.pop();
    } else {
      watches[watch_ix_pos] = &REMOVED_WATCH;
    }
#ifdef MY_DEBUG
    watch_ix_pos = -1;
#endif
  }

  var_++;
  {
    vec<Constr*> &watches = S.watches[var_];
    if (verbosity >= 2) {
      printf("RemoveWatchNeg %d %d %d %d\n", var_, watches.size(), watch_ix_neg, var(old_tag));
    }
#ifdef MY_DEBUG
    std::cout << std::flush; assert(watch_ix_neg >= 0);
#endif
    if (watches.size() == watch_ix_neg + 1) {
      watches.pop();
    } else {
      watches[watch_ix_neg] = &REMOVED_WATCH;
    }
  }
#ifdef MY_DEBUG
  watch_ix_neg = -1;
#endif
}

inline void WatchedPlace::remove_watch_pos(Solver &S, Lit lit) {
  vec<Constr*> &watches = S.watches[index(lit)];
  if (verbosity >= 2) {
    printf("RemoveWatchPos2 %d %d %d\n", watches.size(), watch_ix_pos, var(lit));
  }
#ifdef MY_DEBUG
  std::cout << std::flush; assert(watch_ix_pos >= 0);
#endif
  if (watches.size() == watch_ix_pos + 1) {
    watches.pop();
  } else {
    watches[watch_ix_pos] = &REMOVED_WATCH;
  }
#ifdef MY_DEBUG
  watch_ix_neg = -1;
#endif
}

inline void WatchedPlace::remove_watch_neg(Solver &S, Lit lit) {
  vec<Constr*> &watches = S.watches[index(lit)];
  if (verbosity >= 2) {
    printf("RemoveWatchNeg2 %d %d %d\n", watches.size(), watch_ix_neg, var(lit));
  }
#ifdef MY_DEBUG
  std::cout << std::flush; assert(watch_ix_neg >= 0);
#endif
  if (watches.size() == watch_ix_neg + 1) {
    watches.pop();
  } else {
    watches[watch_ix_neg] = &REMOVED_WATCH;
  }
#ifdef MY_DEBUG
  watch_ix_neg = -1;
#endif
}

WatchedPlace::WatchedPlace(HorLine *hor_)
: Place{hor_, 0, IX_NULL}
{ }
WatchedPlace::WatchedPlace(Place place)
: Place(place)
{ }

void Trie::on_accept(Solver &S) {
  if (is_ver()) ver_accept = true;
  if (verbosity >= 2) printf("ACCEPT_LVL2 %d\n", S.decisionLevel());
}

Trie::Trie()
: WatchedPlace(&root)
, root{{NULL, 0, 0}, vector<VerHead>()}
, root_greater_places()
, my_literals()
, back_ptrs()
, greater_backjumpers()
, greater_stack()
, to_cut{NULL}
{ }

void Trie::init(const vec<Lit> &my_literals_) {
  my_literals.reserve(my_literals_.size());
  for (int i = 0; i < my_literals_.size(); i++) {
    my_literals.push_back(my_literals_[i]);
  }
  back_ptrs.resize(my_literals_.size());
  greater_stack.reserve(my_literals_.size());
}

Lit Trie::guess(Solver &S) {
  if (!ver_accept && !hor_is_out()) {
    Lit out_lit = get_tag();

    if (verbosity >= 2) std::cout << "GREATER_PUSH1 " << S.decisionLevel() << " " << *this << std::endl;

    GreaterBackjumper &backj = new_backjumper();
    backj.greater_places.clear_nodestroy();
    backj.changed_places.clear();
    backj.is_acc = false;
    backj.least_enabled = true;
    backj.least_place = *this;

    S.undos[var(out_lit)].push(this);

    if (verbosity >= 2) {
      printf("GUESS_%s " L_LIT " ", is_ver() ? "VER" : "HOR", L_lit(out_lit));
      std::cout << *this << std::endl;
    }
    return out_lit;
  }
  else if (last_greater.second != IX32_NULL) {
    GreaterPlace &gplace = greater_place_at(last_greater);
    Lit out_lit = gplace.get_tag();
    if (verbosity >= 2) {
      std::cout << "GUESS_GREATER " << gplace << " ";
      printf(L_LIT "\n", L_lit(out_lit));
    }
    if (verbosity >= 2) std::cout << "GREATER_PUSH2 " << S.decisionLevel() << (L_lit(out_lit)) << std::endl;

    GreaterBackjumper &backj = new_backjumper();
    backj.greater_places.clear_nodestroy();
    backj.changed_places.clear();
    backj.is_acc = false;
    backj.least_enabled = false;

    S.undos[var(out_lit)].push(this);
    return out_lit;
  }
  else {
    if (active_var >= my_literals.size()) return lit_Undef;
    active_var_old = active_var;

    do {
      Lit p = my_literals[active_var];
      if (S.value(p) == l_Undef) {
        if (verbosity >= 2) printf("GUESS_ACC %d " L_LIT "\n", active_var, L_lit(p));

        GreaterBackjumper &backj = new_backjumper();
        backj.greater_places.clear_nodestroy();
        backj.changed_places.clear();
        backj.is_acc = true;
        backj.least_enabled = false;

        S.undos[var(p)].push(this);
        back_ptrs[active_var] = active_var_old;
        active_var++;
        return p;
      }
      active_var++;
    } while (active_var < my_literals.size());

    active_var++;
    S.undos[var(S.trail.last())].push(this);
    if (verbosity >= 2) printf("noguess %d\n", active_var_old);
    return lit_Undef;
  }
}

void Trie::onSat(Solver &S) {
  if (verbosity >= 2) std::cout << "ON_SAT " << *this << std::endl;

  unordered_set<int> my_zeroes_set;

  ITER_MY_ZEROES(*this, x,
      my_zeroes_set.insert(index(x));
  )

  // max level of added_vars+my_zeroes
  int max_level = -1;
  int last_but_max_level = -2;

  // added_vars are (level, variable) pairs, of zero variables added in the
  // accepting condition (= not included in my_zeroes)
  vector<std::pair<int, Lit>> added_vars;
  added_vars.reserve(my_literals.size());
  for (Lit x: my_literals) {
    if (S.value(x) == l_False) {
      if (verbosity >= 2) {
        printf("MY_ZERO2 " L_LIT " %d\n", L_lit(x), S.value(x).toInt());
      }
      int lvl = S.level[var(x)];
      if (lvl > max_level) {
        last_but_max_level = max_level;
        max_level = lvl;
      } else if (lvl > last_but_max_level && lvl != max_level) {
        last_but_max_level = lvl;
      }
      if (!my_zeroes_set.contains(index(x))) {
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
    S.cancelUntil(max_level);
    return;
  }

  // sort added_vars by level
  std::sort(added_vars.begin(), added_vars.end());

  if (verbosity >= 2) {
    for (auto x: added_vars) {
       printf(
          "ADDED_VAR %d " L_LIT "\n",
          std::get<0>(x), L_lit(std::get<1>(x))
       );
     }
  }

  HorLine *extended_hor;
  unsigned extended_hor_ix;
  if (ver_accept) {
    // We create a new horizontal empty branch right to the current final place
    // (which is vertical because least_ver_accept is set only when accepting at
    // vertical places).
    HorLine *new_active_hor = new HorLine{*this};
    if (verbosity >= -2) hor_count++;
    assert(deref_ver().hor == NULL);
    deref_ver().hor = new_active_hor;
    extended_hor = new_active_hor;
    extended_hor_ix = 0;
  } else {
    extended_hor = hor;
    extended_hor_ix = hor_ix;
  }

  GreaterIx acc_ix;
  int acc_level;
  int visit_level;

  if (ver_accept) {
    HorHead &horhead = deref_ver();
    acc_ix = horhead.accept_ix;
    acc_level = horhead.accept_level;
    visit_level = horhead.visit_level;
  } else {
    Place back = hor->back_ptr;
    if (back.hor == NULL) {
      acc_ix = root_accept_ix;
      acc_level = root_accept_level;
      visit_level = 0;
    } else {
      HorHead &horhead = back.deref_ver();
      acc_ix = horhead.accept_ix;
      acc_level = horhead.accept_level;
      visit_level = horhead.visit_level;
    }
  }

  if (verbosity >= 2) printf("ACC_IX_LVL_VISIT %d %d %d %d\n", acc_ix.first, acc_ix.second, acc_level, visit_level);


  // Add the first added_var to the current horizontal branch.
  const std::pair<int, Lit>& first_added_var = added_vars[0];
  int previous_var_level = first_added_var.first;
  VerHead &ver_head = extended_hor->elems.emplace_back(first_added_var.second);
  ver_head.hors.reserve(added_vars.size() - 1);
  // Continue down with a vertical branch containing the remaining added_vars.
  for (unsigned i = 1; i < added_vars.size(); i++) {
    pair<int, Lit> added_var = added_vars[i];
    ver_head.hors.emplace_back(added_var.second, max(visit_level, previous_var_level));
    previous_var_level = added_var.first;
  }

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
  // back, to the max level of the remaining literals. Untrue! We jump to the
  // max_level of the remaining literals but we don't cancel that level, we
  // only bind the asserting literal there and continue, so its backjumper does
  // not get called. Anyway, the following paragraph resolves this.
  //
  // (Not so special edge case, read: Why is the lowest place skipped)
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

  vector<pair<int, GreaterIx>> swallow_line;
  GreaterIx new_acc_ix = GREATER_IX_NULL;

  if (TRIE_MODE == branch_always && visit_level != acc_level) {
    // Create a greater place at the top of the added branch

    LogList<GreaterPlace> *incomplete_greater_places;
    unsigned incomplete_backjumper_ix;

    if (visit_level <= S.root_level) {
      incomplete_greater_places = &root_greater_places;
      incomplete_backjumper_ix = IX_NULL;
    } else {
      incomplete_backjumper_ix = visit_level - S.root_level - 1;
      incomplete_greater_places = &greater_backjumpers[incomplete_backjumper_ix].greater_places;
    }

    GreaterIx completion_ix(incomplete_backjumper_ix, incomplete_greater_places->size());
    extended_hor->elems[extended_hor_ix].greater_ix = completion_ix;
    if (verbosity >= 2) printf("WRITE_RIGHT_IX1 %p %d %d %d\n", extended_hor, extended_hor_ix, completion_ix.first, completion_ix.second);
    swallow_line.emplace_back(visit_level, completion_ix);

    GreaterPlace &gplace = incomplete_greater_places->push_back(
      GreaterPlace(
        ChangedGreaterPlace{
          {extended_hor, extended_hor_ix, IX_NULL},
          completion_ix,
          visit_level,
        },
        GREATER_IX_NULL,
        false
      )
    );
    gplace.swallow_ix = acc_ix;
    gplace.swallow_level = acc_level;
    if (acc_level > last_but_max_level) new_acc_ix = completion_ix;
  }

  while (acc_ix.second != IX32_NULL) {
    if (verbosity >= 2) printf("SWALLOW_LINE %d %d %d\n", acc_level, acc_ix.first, acc_ix.second);
    swallow_line.emplace_back(acc_level, acc_ix);
    GreaterPlace &gplace = greater_place_at(acc_ix);
    acc_level = gplace.swallow_level;
    if (acc_level > last_but_max_level && new_acc_ix.second == IX32_NULL) new_acc_ix = acc_ix;
    acc_ix = gplace.swallow_ix;
  }

  // (Not so special edge case, read: Why is the lowest place skipped)
  // We need to be in an accepting state because we don't watch anything.
  // Moreover, there's one special edge case where no backjumper and no reset
  // is called: all my_zeroes are at root_level, except the last one. In that case,
  // the conflict machinery will immediately set the last my_zero to 1 and we
  // should end up in that accepting state. We move there already here.
  hor = extended_hor;
  if (added_vars.size() == 1) {
    ver_accept = false;
    hor_ix = extended_hor_ix + 1;
    ver_ix = IX_NULL;
  } else {
    ver_accept = true;
    hor_ix = extended_hor_ix;
    ver_ix = added_vars.size() - 2;
  }

  if (last_but_max_level >= 0) {
    HorHead &horhead = ver_accept ? deref_ver() : hor->back_ptr.deref_ver();
    horhead.accept_ix = new_acc_ix;
    horhead.accept_level = last_but_max_level;
    horhead.visit_level = last_but_max_level;
  }

  unsigned i = added_vars.size();
  bool populate_backjumpers = i != 1;
  int iter, lvl;

  if (populate_backjumpers) {
    i -= 2;
    lvl = added_vars[i].first;
    if (lvl < S.root_level) {
      populate_backjumpers = false;
      goto after_least;
    }
    iter = lvl - S.root_level;

    for (; iter; lvl--) {
      if (lvl <= acc_level) break;
      --iter;
      GreaterBackjumper &backjumper = greater_backjumpers[iter];
      if (verbosity >= 0) printf("GLVL1 %d\n", lvl);

      for (; i; --i) {
        if (verbosity >= 0) printf("I %d\n", i - 1);
        const std::pair<int, Lit>& added_var = added_vars[i - 1];
        if (added_var.first < lvl) {
          // We don't set the backjumper to the last added var because it will be
          // jumped over yet in onSatConflict.
          if (i + 1 < added_vars.size()) {
            if (verbosity >= 2) {
              printf("LEAST_BACKJUMPER_ENABLE1 %p %d %d\n", extended_hor, extended_hor_ix, i - 1);
            }
            backjumper.least_enabled = true;
            backjumper.least_place = {extended_hor, extended_hor_ix, i - 1};
          }
          goto continue_least;
        }
      }

      // If there is no added_var before the guessed variable, set its backjumper to the
      // start of the added branch.
      if (verbosity >= 2) {
        printf("LEAST_BACKJUMPER_ENABLE2 %p %d %d\n", extended_hor, extended_hor_ix, IX_NULL);
      }
      backjumper.least_enabled = true;
      backjumper.least_place = {extended_hor, extended_hor_ix, IX_NULL};

continue_least: ;
    }
  }
after_least:

  for (
    auto swallow_line_it = swallow_line.rbegin();
    swallow_line_it != swallow_line.rend();
    swallow_line_it++
  ) {
    pair<int, GreaterIx> lvl_ix = *swallow_line_it; 
    GreaterPlace &gplace = greater_place_at(lvl_ix.second);
    if (verbosity >= 0) {
      printf("SWALLOWED_GREATER %d %d %d ", lvl_ix.first, lvl_ix.second.first, lvl_ix.second.second);
      std::cout << gplace << std::endl;
    }

    gplace.hor = extended_hor;
    if (added_vars.size() == 1) {
      gplace.hor_ix = extended_hor_ix + 1;
      gplace.ver_ix = IX_NULL;
    } else {
      gplace.hor_ix = extended_hor_ix;
      gplace.ver_ix = added_vars.size() - 2;
    }
    if (verbosity >= 0) {
      std::cout << "GPLACE_MOVED_TO " << gplace << std::endl;
    }

    if (populate_backjumpers) {
      int original_last_change_level = gplace.last_change_level;
      GreaterBackjumper *next_bjumper = NULL;

      for (; iter; lvl--) {
        if (lvl <= lvl_ix.first) break;
        --iter;
        GreaterBackjumper &backjumper = greater_backjumpers[iter];
        if (verbosity >= 0) printf("GLVL2 %d/%d\n", lvl, S.root_level);

        for (; i; --i) {
          const std::pair<int, Lit>& added_var = added_vars[i - 1];

          if (verbosity >= 0) printf("I %d " L_LIT " %d\n", i - 1, L_lit(added_var.second), added_var.first);

          if (added_var.first < lvl) {
            // We don't set the backjumper to the last added var because it will be
            // jumped over yet in onSatConflict.
            if (i + 1 < added_vars.size()) {
              if (verbosity >= 2) {
                printf("GREATER_BACKJUMPER_ENABLE1 %p %d %d\n", extended_hor, extended_hor_ix, i - 1);
              }
              backjumper.changed_places.push_back({
                {extended_hor, extended_hor_ix, i - 1},
                lvl_ix.second,
                original_last_change_level
              });
              if (next_bjumper) {
                next_bjumper->changed_places.back().last_change_level = lvl;
              } else {
                gplace.last_change_level = lvl;
              }
              next_bjumper = &backjumper;
            }
            goto continue_greater;
          }
        }

        // If there is no added_var before the guessed variable, set its backjumper to the
        // start of the added branch.
        if (verbosity >= 2) {
          printf("GREATER_BACKJUMPER_ENABLE2 %p %d %d\n", extended_hor, extended_hor_ix, IX_NULL);
        }
        backjumper.changed_places.push_back({
          {extended_hor, extended_hor_ix, IX_NULL},
          lvl_ix.second,
          original_last_change_level
        });
        if (next_bjumper) {
          next_bjumper->changed_places.back().last_change_level = lvl;
        } else {
          gplace.last_change_level = lvl;
        }
        next_bjumper = &backjumper;
continue_greater: ;
      }
    }
  }

  S.cancelUntil(max_level);

  if (verbosity >= 2) printf("ACCEPT_LVL1 %d\n", last_but_max_level);
}


WhatToDo Place::after_hors_change(Solver &S) {
  if (hor_is_out()) return WhatToDo::DONE;

  Lit out = deref_hor().tag;
  if (verbosity >= 2) printf("OUTHOR " L_LIT "\n", L_lit(out));
  lbool val = S.value(out);

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
  HorHead &horhead = deref_ver();
  horhead.visit_level = S.decisionLevel();
  Lit out = horhead.tag;
  if (verbosity >= 2) printf("OUTVER " L_LIT "\n", L_lit(out));
  lbool val = S.value(out);

  if (val == l_Undef) {
    return ver_is_last() ? WhatToDo::PROPAGATE : WhatToDo::WATCH;
  }
  if (val == l_False && ver_is_last()) {
    ++ver_ix;
    return WhatToDo::CONFLICT;
  }
  return WhatToDo::AGAIN;
}


GreaterPlace &Place::save_as_greater(Solver &S, bool enabled) {
  Trie &trie = S.trie;

  unsigned backj_size = trie.backjumper_count;
  GreaterIx last_greater = trie.last_greater;
  if (backj_size == 0) {
    GreaterIx ix = pair(IX_NULL, trie.root_greater_places.size());
    ChangedGreaterPlace changed_place = {*this, ix, S.decisionLevel()};
    GreaterPlace &place = trie.root_greater_places.push_back(GreaterPlace(changed_place, last_greater));
    if (enabled) {
      if (trie.last_greater.second != IX32_NULL) {
        trie.root_greater_places[last_greater.second].next = ix;
      }
      trie.last_greater = ix;
      place.set_watch(S);
    } else {
      place.enabled = false;
    }
    return place;
  } else {
    GreaterBackjumper &last_backj = trie.get_last_backjumper();
    GreaterIx ix = pair(backj_size - 1, last_backj.greater_places.size());
    ChangedGreaterPlace changed_place = {*this, ix, S.decisionLevel()};
    GreaterPlace &place = last_backj.greater_places.push_back(GreaterPlace(changed_place, last_greater));
    if (enabled) {
      if (last_greater.second != IX32_NULL) {
        if (last_greater.first == IX_NULL) {
          trie.root_greater_places[last_greater.second].next = ix;
        } else {
          trie.greater_backjumpers[last_greater.first].greater_places[last_greater.second].next = ix;
        }
      }
      trie.last_greater = ix;
      place.set_watch(S);
    } else {
      place.enabled = false;
    }
    return place;
  }
}


void Place::branch(Solver &S) {
  if (is_ver()) {
    HorLine *hor2 = deref_ver().hor;
    if (hor2 == NULL) return;

    if (verbosity >= 2) {
      std::cout << "ADD_TO_GREATER_STACK " << PlaceAttrs(Place{hor2, 0, IX_NULL}, S) << "\n";
    }
    S.trie.greater_stack.emplace_back(hor2, 0);
  } else {
    if (hor_ix + 1 == hor->elems.size()) return;
    if (verbosity >= 2) {
      std::cout << "ADD_TO_GREATER_STACK2 " << PlaceAttrs(Place{hor, hor_ix + 1, IX_NULL}, S) << "\n";
    }
    S.trie.greater_stack.emplace_back(hor, hor_ix + 1);
  }
}


bool GreaterStackItem::handle(Solver &S) {
  Place place = {hor, hor_ix, IX_NULL};
  if (verbosity >= 2) {
    std::cout << "HANDLE_GREATER_STACK " << PlaceAttrs(place, S) << " " << "\n";
  }
  switch (place.multimove_on_propagate(S, place.after_hors_change(S))) {
    case MultimoveEnd::E_WATCH: {
      GreaterPlace &greater = place.save_as_greater(S);
      if (TRIE_MODE == branch_always) {
        hor->elems[hor_ix].greater_ix = greater.ix;
        if (verbosity >= 2) printf("WRITE_RIGHT_IX2 %p %d %d %d\n", hor, hor_ix, greater.ix.first, greater.ix.second);

        if (place.is_ver()) {
          HorLine *hor2 = place.deref_ver().hor;
          if (hor2 == NULL) return true;
          S.trie.greater_stack.emplace_back(hor2, 0);
        } else {
          if (place.hor_ix + 1 == place.hor->elems.size()) return true;
          S.trie.greater_stack.emplace_back(place.hor, place.hor_ix + 1);
        }
      }

      return true;
    }
    case MultimoveEnd::E_DONE: {
      if (TRIE_MODE == branch_always) {
        GreaterPlace &greater = place.save_as_greater(S, false);
        hor->elems[hor_ix].greater_ix = greater.ix;
        if (verbosity >= 2) printf("WRITE_RIGHT_IX3 %p %d %d %d\n", hor, hor_ix, greater.ix.first, greater.ix.second);
        greater.accept_notify_horhead(S);
      }
      return true;
    }
    case MultimoveEnd::E_PROPAGATE: {
      GreaterPlace &greater = place.save_as_greater(S);
      if (TRIE_MODE == branch_always) {
        hor->elems[hor_ix].greater_ix = greater.ix;
        if (verbosity >= 2) printf("WRITE_RIGHT_IX4 %p %d %d %d\n", hor, hor_ix, greater.ix.first, greater.ix.second);
      }
      check(S.enqueue(place.get_tag(), &greater));

      return true;
    }
    default: { // case MultimoveEnd::E_CONFLICT:
      return false;
    }
  }
}


WhatToDo Place::move_on_propagate(Solver &S, Lit out_lit, bool do_branch) {
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
      if (do_branch) branch(S);
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
      if (do_branch) branch(S);
      ver_ix++;
      return after_vers_change(S);
    }
  }
}


MultimoveEnd Place::multimove_on_propagate(Solver &S, WhatToDo what_to_do) {
  Lit out_lit;

  while (true) {
    switch (what_to_do) {
      case AGAIN: {
        if (verbosity >= 2) {
          printf("AGAIN %d %d " L_LIT "\n", hor_ix, ver_ix, L_lit(get_tag()));
        }
        out_lit = get_tag();
        break;
      }

      case WATCH: {
        if (verbosity >= 2) {
          printf("WATCH %d %d " L_LIT "\n", hor_ix, ver_ix, L_lit(get_tag()));
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
          printf("PROPAGATE %d %d " L_LIT "\n", hor_ix, ver_ix, L_lit(get_tag()));
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

    what_to_do = move_on_propagate(S, out_lit, TRIE_MODE != dnf);
  }
}

bool WatchedPlace::full_multimove_on_propagate(Solver &S, WhatToDo what_to_do) {
  MultimoveEnd end = multimove_on_propagate(S, what_to_do);

  Trie &trie = S.trie;

  switch (end) {
    case MultimoveEnd::E_WATCH: {
      set_watch(S);
      if (TRIE_MODE == branch_always) {
        if (is_ver()) {
          HorLine *hor2 = deref_ver().hor;
          if (hor2 == NULL) break;
          trie.greater_stack.emplace_back(hor2, 0);
        } else {
          if (hor_ix + 1 == hor->elems.size()) break;
          trie.greater_stack.emplace_back(hor, hor_ix + 1);
        }
      }
      break;
    }
    case MultimoveEnd::E_DONE: {
      accept_notify_horhead(S);
      on_accept(S);
      break;
    }
    case MultimoveEnd::E_PROPAGATE: {
      set_watch(S);
      check(S.enqueue(get_tag(), this));
      break;
    }
    default: {  // MultimoveEnd::E_CONFLICT
      trie.greater_stack.clear();
      return false;
    }
  }

  while (!trie.greater_stack.empty()) {
    GreaterStackItem gsi = trie.greater_stack.back();
    trie.greater_stack.pop_back();
    if (!gsi.handle(S)) {
      trie.greater_stack.clear();
      return false;
    }
  }

  return true;
}

bool WatchedPlace::propagate(Solver& S, Lit p, bool& keep_watch) {
  if (verbosity >= 2) {
    printf("PROP " L_LIT " ", L_lit(p));
    std::cout << *this << std::endl;
  }
  if (sign(p)) {
    remove_watch_pos(S, ~p);
  } else {
    remove_watch_neg(S, ~p);
  }

  Lit out_lit = get_tag();
  if (TRIE_MODE == branch_always) {
    Trie& trie = S.trie;

    while (true) {
      lbool value = S.value(out_lit);
      if (value == l_True && !ver_is_last()) {
        GreaterIx right_greater_ix;
        if (is_ver()) {
          HorLine *hor2 = deref_ver().hor;
          if (hor2 == NULL) break;
          right_greater_ix = hor2->elems[0].greater_ix;
          if (verbosity >= 2) printf("READ_RIGHT_IX1 %p %d %d %d\n", hor2, 0, right_greater_ix.first, right_greater_ix.second);
        }
        else {
          if (hor_ix + 1 == hor->elems.size()) break;
          right_greater_ix = hor->elems[hor_ix + 1].greater_ix;
          if (verbosity >= 2) printf("READ_RIGHT_IX2 %p %d %d %d\n", hor, hor_ix + 1, right_greater_ix.first, right_greater_ix.second);
        }

        GreaterPlace &right_greater = trie.greater_place_at(right_greater_ix);
        if (verbosity >= 2) std::cout << "JUMP_RIGHT " << right_greater << std::endl;
        *(Place *)this = right_greater;

        right_greater.swallow_ix = my_greater_ix();
        right_greater.swallow_level = S.decisionLevel();

        if (right_greater.enabled) {
          if (trie.backjumper_count) {
            int level = S.decisionLevel();
            if (level != right_greater.last_change_level) {
              GreaterBackjumper &last_backjumper = trie.get_last_backjumper();
              last_backjumper.changed_places.emplace_back(right_greater, right_greater.ix, right_greater.last_change_level);
              right_greater.last_change_level = level;
            }
          }

          out_lit = get_tag();
          right_greater.remove_watch(S, out_lit);
          right_greater.on_accept(S);
        } else {
          if (verbosity >= 2) std::cout << "RIGHT_DISABLED " << right_greater << std::endl;
          on_accept(S);
          return true;
        }
      } else if (value == l_Undef) {
        set_watch(S);
        return true;
      } else break;
    }
  }

  if (verbosity >= 2) printf("OUT_LIT " L_LIT "\n", L_lit(out_lit));
  return full_multimove_on_propagate(S, move_on_propagate(S, out_lit, TRIE_MODE == branch_on_zero));
}


void Trie::undo(Solver& S, Lit p) {
  if (verbosity >= 2) printf("UNDO %d %d %d\n", S.decisionLevel(), S.root_level, backjumper_count);
  if (active_var > my_literals.size()) {
    if (verbosity >= 2) {
      printf("ACTIVE_VAR_UNDO " L_LIT "\n", L_lit(S.outputs[active_var_old]));
      std::cout << std::flush;
    }
    std::cout << std::flush;
    active_var = active_var_old;
    return;
  }

  GreaterBackjumper &backj = get_last_backjumper();
  if (backj.is_acc) {
    active_var--;
    if (verbosity >= 2) {
      printf("ACC_UNDO " L_LIT " " L_LIT "\n", L_lit(S.outputs[active_var]), L_lit(p));
      std::cout << std::flush;
    }
    active_var = back_ptrs[active_var];
  }

  if (backj.least_enabled) {
    if (!ver_accept && !hor_is_out() && !in_conflict()) {
      remove_watch(S, get_tag());
    }
    (Place&)(*this) = backj.least_place;
    ver_accept = false;

    if (verbosity >= 2) {
      printf("LEAST_UNDO %d %d %lu\n", backj.least_place.hor_ix, backj.least_place.ver_ix, backj.least_place.hor->elems.size());
    }
    Lit out_lit = backj.least_place.get_tag();
    set_watch(S);
    if (verbosity >= 2) printf("WU " L_LIT "\n", L_lit(out_lit));
  }

  if (verbosity >= 2) {
    std::cout << "GREATER_UNDO "
        << backj.greater_places.size() << " "
        << backj.changed_places.size() << "\n"
        << std::flush;
  }

  ITER_LOGLIST(backj.greater_places, GreaterPlace, {
    GreaterPlace &gplace = x;
    if (gplace.enabled) {
      if (!gplace.in_conflict()) {
        if (verbosity >= 2) {
          std::cout << "REMOVE_GREATER " << gplace << " ";
          printf(L_LIT, L_lit(gplace.get_tag()));
          std::cout << std::endl << std::flush;
        }
        gplace.remove_watch(S, gplace.get_tag());
      } else if (verbosity >= 2) {
        std::cout << "UNTANGLE_GREATER " << gplace << std::endl << std::flush;
      }

      if (gplace.previous.second != IX32_NULL) greater_place_at(gplace.previous).next = gplace.next;
      if (gplace.next.second == IX32_NULL) last_greater = gplace.previous;
      else greater_place_at(gplace.next).previous = gplace.previous;
    } else if (verbosity >= 2) {
        std::cout << "SKIP_GREATER " << gplace << std::endl << std::flush;
    }
  })

  for (ChangedGreaterPlace changed_place: backj.changed_places) {
    GreaterPlace &gplace = greater_place_at(changed_place.ix);

    if (verbosity >= 2) {
      std::cout << "CHANGED " << gplace << " " << changed_place.place
        << " " << changed_place.ix.first << "," << changed_place.ix.second << "\n" << std::flush;
    }

    if (gplace.enabled) {
      if (!gplace.in_conflict()) {
        gplace.remove_watch(S, gplace.get_tag());
      }
      (Place &)gplace = changed_place.place;
      gplace.last_change_level = changed_place.last_change_level;
    } else {
      (Place &)gplace = changed_place.place;
      gplace.enabled = true;
      gplace.last_change_level = changed_place.last_change_level;

      gplace.previous = last_greater;
      gplace.next = GREATER_IX_NULL;
      if (last_greater.second != IX32_NULL) greater_place_at(last_greater).next = changed_place.ix;
      last_greater = changed_place.ix;
    }

    gplace.set_watch(S);
  }

  --backjumper_count;
}


GreaterBackjumper& Trie::new_backjumper() {
  unsigned ix = backjumper_count;
  ++backjumper_count;

  if (ix == greater_backjumpers.size()) {
    return greater_backjumpers.emplace_back();
  } else {
    return greater_backjumpers[ix];
  }
}


void WatchedPlace::calcReason(Solver& S, Lit p, vec<Lit>& out_reason) {
  if (p == lit_Undef) {
    int max_level = -1;
    ITER_MY_ZEROES(*this, x,
      max_level = max(max_level, S.level[var(x)]);
      out_reason.push(~x);
    )

    if (verbosity >= 2) {
      printf("CALC_REASON_CONFLICT");
      ITER_MY_ZEROES(*this, x, printf(" " L_LIT, L_lit(x));)
      printf("\n");
    }

    S.cancelUntil(max_level);
  }
  else {
    Place place(*this);
    if (in_conflict()) place.ver_ix--;
    else if (hor_is_out()) place.hor_ix--;
    while (place.get_tag() != p) {
      if (place.is_ver()) {
        place.ver_ix = IX_NULL;
      }
      if (place.hor_ix) {
        place.hor_ix--;
      } else {
        place = place.hor->back_ptr;
      }
    }
    ITER_MY_ZEROES(place, x,
      out_reason.push(~x);
    )

    if (verbosity >= 2) {
      printf("CALC_REASON_PLACE " L_LIT " ", L_lit(p));
      std::cout << place << " " << *this;
      ITER_MY_ZEROES(place, x,
          printf(" " L_LIT, L_lit(x));
      )
      printf("\n");
    }
  }
}

GreaterPlace& Trie::greater_place_at(GreaterIx ix) {
  if (verbosity >= 2) printf("GREATER_PLACE_AT %d %d\n", ix.first, ix.second);
  return ix.first == IX_NULL
    ? root_greater_places[ix.second]
    : greater_backjumpers[ix.first].greater_places[ix.second];
}

bool Trie::reset(Solver &S) {
  if (!ver_accept && !hor_is_out() && !in_conflict()) {
    remove_watch(S, get_tag());
  }

  {
    GreaterIx greater_ix = last_greater;
    while (true) {
      if (greater_ix.second == IX32_NULL) break;
      if (verbosity >= 2) printf("ResettingGreater %d,%d\n", greater_ix.first, greater_ix.second);
      GreaterPlace &gplace = greater_place_at(greater_ix);
      if (!gplace.in_conflict()) {
        gplace.remove_watch(S, gplace.get_tag());
      }
      greater_ix = gplace.previous;
    }
  }
  root_greater_places.clear_nodestroy();
  last_greater = GREATER_IX_NULL;

  hor = &root;
  hor_ix = 0;
  ver_ix = IX_NULL;

  active_var = 0;
  active_var_old = 0;
  ver_accept = false;

  if (verbosity >= 2) printf("RESET\n");

  if (to_cut.hor != NULL) {
    to_cut.cut_away();
    to_cut.hor = NULL;
  }

  return full_multimove_on_propagate(S, after_hors_change(S));
}

GreaterPlace::GreaterPlace(
  ChangedGreaterPlace changed_place, GreaterIx previous_
)
: WatchedPlace(changed_place.place)
, ix(changed_place.ix)
, last_change_level(changed_place.last_change_level)
, previous(previous_)
, next(GREATER_IX_NULL)
{ }

GreaterPlace::GreaterPlace(
  ChangedGreaterPlace changed_place, GreaterIx previous_, bool enabled_
)
: WatchedPlace(changed_place.place)
, ix(changed_place.ix)
, last_change_level(changed_place.last_change_level)
, previous(previous_)
, next(GREATER_IX_NULL)
, enabled(enabled_)
{ }


void GreaterPlace::on_accept(Solver &S) {
  enabled = false;

  Trie &trie = S.trie;
  if (previous.second != IX32_NULL) trie.greater_place_at(previous).next = next;
  if (next.second == IX32_NULL) trie.last_greater = previous;
  else trie.greater_place_at(next).previous = previous;
}


bool GreaterPlace::propagate(Solver &S, Lit p, bool& keep_watch) {
  Trie& trie = S.trie;
  if (trie.backjumper_count) {
    int level = S.decisionLevel();
    if (level != last_change_level) {
      if (verbosity >= 2) {
        std::cout << "GREATER_BACKJUMPER_ENABLE3 "
          << level << " " << last_change_level << " "
          << *this << " " << ix.first << " " << ix.second << std::endl;
      }
      trie.get_last_backjumper().changed_places.emplace_back(*this, ix, last_change_level);
      last_change_level = level;
    }
  }
  return WatchedPlace::propagate(S, p, keep_watch);
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
  Lit out = p.get_tag();
  return
    os << "["
    << "label=\"" << (sign(out) ? "~" : "") << var(out) << "\","
    << "tooltip=" << (Place&)p
    << "]";
}

void Trie::print_places() {
    std::cout << "LEAST_PLACE " << (Place &)(*this) << " " << in_conflict() << std::endl;
    ITER_LOGLIST(root_greater_places, GreaterPlace, {
      std::cout << "GREATER_PLACE -1 " << (Place &)x << " " << x.enabled << " " << x.in_conflict() << std::endl;
    })
    unsigned i = 0;
    for (GreaterBackjumper& backj: greater_backjumpers) {
      ITER_LOGLIST(backj.greater_places, GreaterPlace, {
        std::cout << "GREATER_PLACE " << i << " " << (Place &)x << " " << x.enabled << " " << x.in_conflict() << std::endl;
      })
      ++i;
    }
}
