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
Mode TRIE_MODE = branch_always;

void check_duplicate_places(Trie &trie, RearGuard &p) {
  ITER_LOGLIST(trie.root_new_rears, RearGuard, x, {
    assert(x.ix == p.ix || x.hor != p.hor || x.hor_ix != p.hor_ix || x.ver_ix != p.ver_ix);
  })
  unsigned i = 0;
  for (int j = 0; j < trie.snapshot_count; ++j) {
    Snapshot& snapshot = trie.snapshots[j];
    ITER_LOGLIST(snapshot.new_rears, RearGuard, x, {
      assert(x.ix == p.ix || x.hor != p.hor || x.hor_ix != p.hor_ix || x.ver_ix != p.ver_ix);
    })
    ++i;
  }
}

void check_all_duplicate_places(Trie &trie) {
  ITER_LOGLIST(trie.root_new_rears, RearGuard, x, {
    check_duplicate_places(trie, x);
  })
  unsigned i = 0;
  for (int j = 0; j < trie.snapshot_count; ++j) {
    Snapshot& snapshot = trie.snapshots[j];
    ITER_LOGLIST(snapshot.new_rears, RearGuard, x, {
      check_duplicate_places(trie, x);
    })
    ++i;
  }
}

void check_unique_rear_snapshot(Snapshot &snapshot, GuardIx ix) {
  std::cout << std::flush;
  for (RearSnapshot &rear_snapshot: snapshot.rear_snapshots) {
    assert(rear_snapshot.ix != ix);
  }
}

#ifdef MY_DEBUG
#define CHECK_ALL_DUPLICATE_PLACES(trie) check_all_duplicate_places(trie)
#else
#define CHECK_ALL_DUPLICATE_PLACES(trie)
#endif

#ifdef MY_DEBUG
#define CHECK_UNIQUE_REAR_SNAPSHOT(snapshot, ix) check_unique_rear_snapshot(snapshot, ix)
#else
#define CHECK_UNIQUE_REAR_SNAPSHOT(snapshot, ix)
#endif

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

  ++var_;
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

  ++var_;
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

WatchedPlace::WatchedPlace(Place place)
: Place(place)
{ }

Trie::Trie()
: root{Place(NULL, 0, 0), vector<VerHead>()}
, root_new_rears()
, root_reasons()
, my_literals()
, back_ptrs()
, snapshots()
, rear_stack()
, to_cut(NULL, 0, 0)
{ }

bool Trie::init(const vec<Lit>& my_literals_, const unordered_set<unsigned>& init_clause_omits) {
  my_literals.reserve(my_literals_.size());
  for (int i = 0; i < my_literals_.size(); ++i) {
    my_literals.push_back(my_literals_[i]);
  }
  back_ptrs.resize(my_literals_.size());
  rear_stack.reserve(my_literals_.size());

  VerHead *ver_head = NULL;
  int depth = 0;
  unsigned i = 0;
  for (; i < my_literals.size(); ++i) {
    if (!init_clause_omits.contains(i)) {
      ver_head = &root.elems.emplace_back(my_literals[0]);
      break;
    }
  }

  if (ver_head == NULL) return false;

  // Continue down with a vertical branch containing the remaining added_vars.
  for (++i; i < my_literals.size(); ++i) {
    if (!init_clause_omits.contains(i)) {
      ver_head->hors.emplace_back(my_literals[i], 0, ++depth);
    }
  }

  RearSnapshot rear_snapshot = {Place(&root, 0, IX_NULL), GREATER_IX_FIRST, 0};
  RearGuard &root_place = root_new_rears.push_back(
    RearGuard(rear_snapshot, GREATER_IX_NULL, true)
  );

  return true;
}

bool Trie::guess(Solver &S) {
  CHECK_ALL_DUPLICATE_PLACES(*this);

  if (last_rear.second != IX32_NULL) {
    RearGuard &rguard = rear_guard_at(last_rear);
    Lit out_lit = rguard.get_tag();
    if (verbosity >= 2) {
      std::cout << "GUESS_GREATER " << rguard << " " << &rguard << " ";
      printf(L_LIT "\n", L_lit(out_lit));
    }
    if (verbosity >= 2) std::cout << "GREATER_PUSH2 " << S.decisionLevel() << (L_lit(out_lit)) << std::endl;
#ifdef MY_DEBUG
    assert(rguard.enabled);
    assert(!rguard.in_conflict());
#endif

    Snapshot &snapshot = new_snapshot();
    snapshot.is_acc = false;

    S.assume(out_lit);
    S.undos.push_back(this);
    return true;
  }
  else {
    if (active_var >= my_literals.size()) return false;
    active_var_old = active_var;

    do {
      Lit p = my_literals[active_var];
      if (S.value(p) == l_Undef) {
        if (verbosity >= 2) printf("GUESS_ACC %d " L_LIT "\n", active_var, L_lit(p));

        Snapshot &snapshot = new_snapshot();
        snapshot.is_acc = true;

        back_ptrs[active_var] = active_var_old;
        ++active_var;
        S.assume(p);
        S.undos.push_back(this);
        return true;
      }
      ++active_var;
    } while (active_var < my_literals.size());

    ++active_var;
    if (verbosity >= 2) printf("noguess %d\n", active_var_old);
    S.undos.push_back(this);
    return false;
  }
}

void Trie::onSat(Solver &S) {
  CHECK_ALL_DUPLICATE_PLACES(*this);

  accept_place->onSat(S, accept_level);

  CHECK_ALL_DUPLICATE_PLACES(*this);
}

void RearGuard::onSat(Solver &S, int accept_level) {
  Trie &trie = S.trie;

  if (verbosity >= 2) {
    std::cout << "ON_SAT " << *this << " " << S.root_level << " " << accept_level
      << " " << this << " " << ix.first << "," << ix.second << " " << trie.root_new_rears.size();
    for (int i = 0; i < trie.snapshot_count; ++i) {
      Snapshot &snapshot = trie.snapshots[i];
      std::cout << "," << snapshot.new_rears.size();
    }
    std::cout << std::endl;
  }

  unordered_set<int> my_zeroes_set;

  ITER_MY_ZEROES(*this, x,
      if (verbosity >= 2) {
        printf("MY_ZERO1 " L_LIT " %d %d\n", L_lit(x), S.value(x).toInt(), S.level[var(x)]);
        std::cout << std::flush;
      }
      my_zeroes_set.insert(index(x));
#ifdef MY_DEBUG
      assert(S.value(x) == l_False);
#endif
  )

  // max level of added_vars+my_zeroes
  int max_level = -1;
  int last_but_max_level = -2;

  // added_vars are (level, variable) pairs, of zero variables added in the
  // accepting condition (= not included in my_zeroes)
  vector<std::pair<int, Lit>> added_vars;
  added_vars.reserve(trie.my_literals.size());
  for (Lit x: trie.my_literals) {
    if (S.value(x) == l_False) {
      if (verbosity >= 2) {
        printf("MY_ZERO2 " L_LIT " %d %d\n", L_lit(x), S.value(x).toInt(), S.level[var(x)]);
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

  bool ver_accept = is_ver();

  // We have found a solution that covers the last traversed clause => we
  // shrink the clause (cut it up to the knee) instead of adding a new branch
  // to the trie.
  if (added_vars.size() == 0) {
    if (verbosity >= 2) printf("NO_ADDED_VAR\n");
    trie.to_cut = ver_accept ? *this : hor->back_ptr;
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
    extended_hor = deref_ver().hor;
    if (extended_hor == NULL) {
      // We create a new horizontal empty branch right to the current final place
      // (which is vertical because least_ver_accept is set only when accepting at
      // vertical places).
      extended_hor = new HorLine{*this};
      if (verbosity >= -2) ++hor_count;
      deref_ver().hor = extended_hor;
      extended_hor_ix = 0;
    } else {
      extended_hor_ix = extended_hor->elems.size();
    }
  } else {
    extended_hor = hor;
    extended_hor_ix = extended_hor->elems.size();
  }

  int visit_level;
  int depth;

  if (ver_accept) {
    HorHead &horhead = deref_ver();
    visit_level = horhead.visit_level;
    depth = horhead.depth;
  } else {
    Place back = hor->back_ptr;
    if (back.hor == NULL) {
      visit_level = 0;
      depth = 0;
    } else {
      HorHead &horhead = back.deref_ver();
      visit_level = horhead.visit_level;
      depth = horhead.depth;
    }
  }

#ifdef MY_DEBUG
  {
    std::cout << std::flush;
    Lit first_lit = added_vars[0].second;
    if (ver_accept) {
      HorHead &horhead = deref_ver();
      assert(horhead.tag != first_lit);
    } else {
      Place back = hor->back_ptr;
      if (back.hor != NULL) {
        HorHead &horhead = back.deref_ver();
        assert(horhead.tag != first_lit);
      }
    }
    for (VerHead &verhead: extended_hor->elems) {
      assert(verhead.tag != first_lit);
    }
  }
#endif

  if (verbosity >= 2) printf("ACC_LVL_VISIT %d %d\n", accept_level, visit_level);


  // Add the first added_var to the current horizontal branch.
  const std::pair<int, Lit>& first_added_var = added_vars[0];
  int previous_var_level = first_added_var.first;
  VerHead &ver_head = extended_hor->elems.emplace_back(first_added_var.second);
  ver_head.hors.reserve(added_vars.size() - 1);
  // Continue down with a vertical branch containing the remaining added_vars.
  for (unsigned i = 1; i < added_vars.size(); ++i) {
    pair<int, Lit> added_var = added_vars[i];
    ver_head.hors.emplace_back(added_var.second, max(visit_level, previous_var_level), ++depth);
    previous_var_level = added_var.first;
  }

  // For each guess, find the least place in the newly
  // created branch, that has higher or equal level as the guess. If such place
  // exists and if it is not the lowest place, set the guess' snapshot to
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
  // only bind the asserting literal there and continue, so its snapshot does
  // not get called. Anyway, the following paragraph resolves this.
  //
  // (Not so special edge case, read: Why is the lowest place skipped)
  // A special edge case occurs if there is nowhere further back to jump - all
  // the other my_zeroes have been added through input assumptions. In that
  // case however, the last added_var is forced to 1 via conflict analysis (it
  // is the asserting literal), there is no snapshot and the trie remains
  // correctly in the ver_accept state at the last added_var.

  // We go from the lastly guessed variable to the firstly guessed one.
  // To each guessed variable, we assign a snapshot that points to the
  // last place with a level lower than the level of the guessed variable.
  //
  // Why is this so complicated? Shouldn't that always be just the added_var
  // immediately before the guessed added var? No because guessed variables are
  // of course not in added_vars, as they are 1-valued.

  RearGuard *rguard;

  if (visit_level == accept_level) {
    rguard = this;
    enabled = true;
    hor = extended_hor;
    hor_ix = extended_hor_ix;
    ver_ix = (unsigned)added_vars.size() - 1;
    trie.last_rear = ix;
    next = previous = GREATER_IX_NULL;
    if (verbosity >= 2) {
      std::cout << "REUSING_GREATER_PLACE " << (Place &)*this
        << " " << ix.first << "," << ix.second << " " << last_change_level << std::endl;
    }
  } else {
    // Create a rear guard at the top of the added branch
    LogList<RearGuard> *incomplete_rguards;
    unsigned incomplete_snapshot_ix;

    if (visit_level <= S.root_level) {
      incomplete_rguards = &trie.root_new_rears;
      incomplete_snapshot_ix = IX_NULL;
    } else {
      incomplete_snapshot_ix = visit_level - S.root_level - 1;
      incomplete_rguards = &trie.snapshots[incomplete_snapshot_ix].new_rears;
    }

    GuardIx completion_ix(incomplete_snapshot_ix, incomplete_rguards->size());
    if (verbosity >= 2) printf("WRITE_RIGHT_IX1 %p %d %d %d\n", extended_hor, extended_hor_ix, completion_ix.first, completion_ix.second);

    // Put the new rear guard into conflict at the end of the added branch
    rguard = &incomplete_rguards->push_back(
      RearGuard(
        RearSnapshot{
          {extended_hor, extended_hor_ix, (unsigned)added_vars.size() - 1},
          completion_ix,
          visit_level,
        },
        GREATER_IX_NULL,
        true
      )
    );
    if (verbosity >= 2) std::cout << "NEW_GREATER_PLACE3 " << rguard << std::endl;
    trie.last_rear = completion_ix;
  }

  unsigned i = added_vars.size() - 1;

  {
    GuardIx gplace_ix = rguard->ix;
    // if (i) --i;
    int lvl = added_vars[i].first;
    if (verbosity >= 2) printf("LVLLVL %d\n", lvl);
    if (lvl < S.root_level) goto break_rear;
    int original_last_change_level = rguard->last_change_level;
    Snapshot *next_bjumper = NULL;

    for (int iter = lvl - S.root_level; iter; --lvl) {
      if (lvl <= visit_level) break;
      --iter;
      Snapshot &snapshot = trie.snapshots[iter];
      if (verbosity >= 0) printf("GLVL2 %d/%d\n", lvl, S.root_level);

      for (; i; --i) {
        const std::pair<int, Lit>& added_var = added_vars[i - 1];

        if (verbosity >= 0) printf("I %d " L_LIT " %d\n", i - 1, L_lit(added_var.second), added_var.first);

        if (added_var.first < lvl) {
          if (verbosity >= 2) {
            printf("GREATER_BACKJUMPER_ENABLE1 %p %d %d\n", extended_hor, extended_hor_ix, i - 1);
          }
          CHECK_UNIQUE_REAR_SNAPSHOT(snapshot, gplace_ix);
          snapshot.rear_snapshots.push_back({
            {extended_hor, extended_hor_ix, i - 1},
            gplace_ix,
            original_last_change_level
          });
          if (next_bjumper) {
            next_bjumper->rear_snapshots.back().last_change_level = lvl;
          } else {
            rguard->last_change_level = lvl;
          }
          next_bjumper = &snapshot;
          goto continue_rear;
        }
      }

      // If there is no added_var before the guessed variable, set its snapshot to the
      // start of the added branch.
      if (verbosity >= 2) {
        printf("GREATER_BACKJUMPER_ENABLE2 %p %d %d\n", extended_hor, extended_hor_ix, IX_NULL);
      }
      CHECK_UNIQUE_REAR_SNAPSHOT(snapshot, gplace_ix);
      snapshot.rear_snapshots.push_back({
        {extended_hor, extended_hor_ix, IX_NULL},
        gplace_ix,
        original_last_change_level
      });
      if (next_bjumper) {
        next_bjumper->rear_snapshots.back().last_change_level = lvl;
      } else {
        rguard->last_change_level = lvl;
      }
      next_bjumper = &snapshot;
continue_rear: ;
    }
  }
break_rear:

  S.cancelUntil(max_level);

  if (verbosity >= 2) printf("ACCEPT_LVL1 %d\n", last_but_max_level);
}


WhatToDo Place::after_hors_change(Solver &S) {
  Lit out = deref_hor().tag;
  if (verbosity >= 2) printf("OUTHOR " L_LIT "\n", L_lit(out));
  lbool val = S.value(out);

  if (val == l_Undef) {
    return ver_is_singleton() ? WhatToDo::PROPAGATE : WhatToDo::WATCH;
  }
  if (val == l_False && ver_is_singleton()) {
    ver_ix = 0;
    CHECK_ALL_DUPLICATE_PLACES(S.trie);
    return WhatToDo::CONFLICT;
  }
  return WhatToDo::AGAIN;
}


WhatToDo Place::after_vers_change(Solver &S) {
  HorHead &horhead = deref_ver();
  horhead.visit_level = S.decisionLevel();

  if (verbosity >= 2) {
    std::cout << "VISIT_LEVEL3 "
      << *this << " "
      << S.decisionLevel()
      << std::endl;
  }

  Lit out = horhead.tag;
  if (verbosity >= 2) printf("OUTVER " L_LIT "\n", L_lit(out));
  lbool val = S.value(out);

  if (val == l_Undef) {
    return ver_is_last() ? WhatToDo::PROPAGATE : WhatToDo::WATCH;
  }
  if (val == l_False && ver_is_last()) {
    ++ver_ix;
    CHECK_ALL_DUPLICATE_PLACES(S.trie);
    return WhatToDo::CONFLICT;
  }
  return WhatToDo::AGAIN;
}


RearGuard &Place::save_as_rear(Solver &S, bool enabled) {
  Trie &trie = S.trie;

  unsigned snapshot_size = trie.snapshot_count;
  GuardIx last_rear = trie.last_rear;
  if (snapshot_size == 0) {
    GuardIx ix = pair(IX_NULL, trie.root_new_rears.size());
    RearSnapshot rear_snapshot = {*this, ix, S.decisionLevel()};
    RearGuard &place = trie.root_new_rears.push_back(RearGuard(rear_snapshot, last_rear));
    if (verbosity >= 2) std::cout << "NEW_GREATER_PLACE1 " << &place << std::endl;
    if (enabled) {
      if (trie.last_rear.second != IX32_NULL) {
        trie.root_new_rears[last_rear.second].next = ix;
      }
      trie.last_rear = ix;
      place.set_watch(S);
    } else {
      place.enabled = false;
    }
    CHECK_ALL_DUPLICATE_PLACES(trie);
    return place;
  } else {
    Snapshot &last_snapshot = trie.get_last_snapshot();
    GuardIx ix = pair(snapshot_size - 1, last_snapshot.new_rears.size());
    RearSnapshot rear_snapshot = {*this, ix, S.decisionLevel()};
    RearGuard &place = last_snapshot.new_rears.push_back(RearGuard(rear_snapshot, last_rear));
    if (verbosity >= 2) std::cout << "NEW_GREATER_PLACE2 " << &place << std::endl;
    if (enabled) {
      if (last_rear.second != IX32_NULL) {
        if (last_rear.first == IX_NULL) {
          trie.root_new_rears[last_rear.second].next = ix;
        } else {
          trie.snapshots[last_rear.first].new_rears[last_rear.second].next = ix;
        }
      }
      trie.last_rear = ix;
      place.set_watch(S);
    } else {
      place.enabled = false;
    }
    CHECK_ALL_DUPLICATE_PLACES(trie);
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
    S.trie.rear_stack.emplace_back(hor2, 0);
  } else {
    if (hor_ix + 1 == hor->elems.size()) return;
    if (verbosity >= 2) {
      std::cout << "ADD_TO_GREATER_STACK2 " << PlaceAttrs(Place{hor, hor_ix + 1, IX_NULL}, S) << "\n";
    }
    S.trie.rear_stack.emplace_back(hor, hor_ix + 1);
  }
}


bool RearStackItem::handle(Solver &S) {
  Place place = {hor, hor_ix, IX_NULL};
  if (verbosity >= 2) {
    std::cout << "HANDLE_GREATER_STACK " << PlaceAttrs(place, S) << " " << "\n";
  }
  switch (place.multimove_on_propagate(S, place.after_hors_change(S))) {
    case MultimoveEnd::E_WATCH: {
      RearGuard &rguard = place.save_as_rear(S);
      if (verbosity >= 2) printf("WRITE_RIGHT_IX2 %p %d %d %d\n", hor, hor_ix, rguard.ix.first, rguard.ix.second);

      if (place.is_ver()) {
        HorLine *hor2 = place.deref_ver().hor;
        if (hor2 == NULL) return true;
        S.trie.rear_stack.emplace_back(hor2, 0);
      } else {
        if (place.hor_ix + 1 == place.hor->elems.size()) return true;
        S.trie.rear_stack.emplace_back(place.hor, place.hor_ix + 1);
      }

      return true;
    }
    case MultimoveEnd::E_DONE: {
      RearGuard &rguard = place.save_as_rear(S, false);
      if (verbosity >= 2) printf("WRITE_RIGHT_IX3 %p %d %d %d\n", hor, hor_ix, rguard.ix.first, rguard.ix.second);
      rguard.on_accept(S);
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
        CHECK_ALL_DUPLICATE_PLACES(S.trie);
        return after_hors_change(S);
      }
    }
    else {
      if (do_branch) branch(S);
      ++ver_ix;
      CHECK_ALL_DUPLICATE_PLACES(S.trie);
      return after_vers_change(S);
    }
  }
  else {
    if (S.value(out_lit) == l_True) {
      if (hor_ix + 1 == hor->elems.size()) return WhatToDo::DONE;
      ++hor_ix;
      CHECK_ALL_DUPLICATE_PLACES(S.trie);
      return after_hors_change(S);
    }
    else {
      if (do_branch) branch(S);
      ++ver_ix;
      CHECK_ALL_DUPLICATE_PLACES(S.trie);
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

        Trie &trie = S.trie;
        if (!trie.snapshot_count) {
          check(S.enqueue(get_tag(), &trie.root_reasons.push_back(Place(hor, hor_ix, ver_ix))));
        } else {
          Snapshot &snapshot = trie.get_last_snapshot();
          check(S.enqueue(get_tag(), &snapshot.reasons.push_back(Place(hor, hor_ix, ver_ix))));
        }

        if (is_ver()) {
          HorLine *hor2 = deref_ver().hor;
          if (hor2 == NULL) what_to_do = DONE;
          else {
            hor = hor2;
            hor_ix = 0;
            ver_ix = IX_NULL;
            CHECK_ALL_DUPLICATE_PLACES(trie);
            what_to_do = after_hors_change(S);
          }
        }
        else {
          if (hor_ix + 1 == hor->elems.size()) return MultimoveEnd::E_DONE;
          ++hor_ix;
          CHECK_ALL_DUPLICATE_PLACES(trie);
          what_to_do = after_hors_change(S);
        }
        continue;
      }

      case CONFLICT: {
        if (verbosity >= 2) {
          printf("CONFLICT %d %d\n", hor_ix, ver_ix);
        }
        return MultimoveEnd::E_CONFLICT;
      }
    }

    what_to_do = move_on_propagate(S, out_lit, true);
  }
}

Reason* WatchedPlace::full_multimove_on_propagate(Solver &S, WhatToDo what_to_do) {
  MultimoveEnd end = multimove_on_propagate(S, what_to_do);

  Trie &trie = S.trie;

  switch (end) {
    case MultimoveEnd::E_WATCH: {
      set_watch(S);
      if (is_ver()) {
        HorLine *hor2 = deref_ver().hor;
        if (hor2 == NULL) break;
        trie.rear_stack.emplace_back(hor2, 0);
      } else {
        if (hor_ix + 1 == hor->elems.size()) break;
        trie.rear_stack.emplace_back(hor, hor_ix + 1);
      }
      break;
    }
    case MultimoveEnd::E_DONE: {
      on_accept(S);
      break;
    }
    default: {  // MultimoveEnd::E_CONFLICT
      trie.rear_stack.clear();
      CHECK_ALL_DUPLICATE_PLACES(trie);
      return this;
    }
  }

  while (!trie.rear_stack.empty()) {
    RearStackItem rsi = trie.rear_stack.back();
    trie.rear_stack.pop_back();
    if (!rsi.handle(S)) {
      trie.rear_stack.clear();
      CHECK_ALL_DUPLICATE_PLACES(trie);
      return this;
    }
  }

  CHECK_ALL_DUPLICATE_PLACES(trie);
  return NULL;
}

Reason* WatchedPlace::propagate(Solver& S, Lit p, bool& keep_watch) {
  if (verbosity >= 2) {
    printf("PROP " L_LIT " ", L_lit(p));
    std::cout << *this << " " << this << std::endl;
  }
  if (sign(p)) {
    remove_watch_pos(S, ~p);
  } else {
    remove_watch_neg(S, ~p);
  }

  Lit out_lit = get_tag();
  Trie& trie = S.trie;

  lbool value = S.value(out_lit);

  if (value == l_True) {
    if (verbosity >= 2) std::cout << "RIGHT_ACCEPT" << std::endl;
    on_accept(S);
    CHECK_ALL_DUPLICATE_PLACES(trie);
    return NULL;
  }

  if (verbosity >= 2) printf("OUT_LIT " L_LIT "\n", L_lit(out_lit));
  CHECK_ALL_DUPLICATE_PLACES(trie);
  return full_multimove_on_propagate(S, move_on_propagate(S, out_lit, false));
}


void Trie::undo(Solver& S) {
  if (verbosity >= 2) printf("UNDO %d %d %d\n", S.decisionLevel(), S.root_level, snapshot_count);
  if (active_var > my_literals.size()) {
    if (verbosity >= 2) {
      printf("ACTIVE_VAR_UNDO " L_LIT "\n", L_lit(S.outputs[active_var_old]));
      std::cout << std::flush;
    }
    std::cout << std::flush;
    active_var = active_var_old;
    return;
  }

  Snapshot &snapshot = get_last_snapshot();
  if (snapshot.is_acc) {
    active_var--;
    if (verbosity >= 2) {
      printf("ACC_UNDO " L_LIT "\n", L_lit(S.outputs[active_var]));
      std::cout << std::flush;
    }
    active_var = back_ptrs[active_var];
  }

  if (verbosity >= 2) {
    std::cout << "GREATER_UNDO "
        << snapshot.new_rears.size() << " "
        << snapshot.rear_snapshots.size() << "\n"
        << std::flush;
  }

  ITER_LOGLIST(snapshot.new_rears, RearGuard, rguard, {
    if (rguard.enabled) {
      if (!rguard.in_conflict()) {
        if (verbosity >= 2) {
          std::cout << "REMOVE_GREATER " << rguard << " ";
          printf(L_LIT, L_lit(rguard.get_tag()));
          std::cout << " " << &rguard << std::endl << std::flush;
        }
        rguard.remove_watch(S, rguard.get_tag());
      } else if (verbosity >= 2) {
        std::cout << "UNTANGLE_GREATER " << rguard << " " << &rguard << std::endl << std::flush;
      }

      rguard.enabled = false;  // TODO backport the fix
      if (rguard.previous.second != IX32_NULL) rear_guard_at(rguard.previous).next = rguard.next;
      if (rguard.next.second == IX32_NULL) last_rear = rguard.previous;
      else rear_guard_at(rguard.next).previous = rguard.previous;
    } else if (verbosity >= 2) {
        std::cout << "SKIP_GREATER " << rguard << " " << &rguard << std::endl << std::flush;
    }
  })

  for (RearSnapshot rear_snapshot: snapshot.rear_snapshots) {
    RearGuard &rguard = rear_guard_at(rear_snapshot.ix);

    if (verbosity >= 2) {
      std::cout << "CHANGED " << &rguard << " " << rguard << " " << rear_snapshot.place
        << " " << rear_snapshot.ix.first << "," << rear_snapshot.ix.second
        << " " << rguard.enabled << " LCLVL "
        << rguard.last_change_level << "->" << rear_snapshot.last_change_level
        << "\n" << std::flush;
    }

    bool watch_unwatch = false;
    Lit new_tag = rear_snapshot.place.get_tag();

    if (rguard.enabled) {
      if (!rguard.in_conflict()) {
        Lit old_tag = rguard.get_tag();
        if (old_tag == new_tag) {
          watch_unwatch = true;
        } else {
          rguard.remove_watch(S, rguard.get_tag());
        }
      }
      (Place &)rguard = rear_snapshot.place;
      rguard.last_change_level = rear_snapshot.last_change_level;
    } else {
      (Place &)rguard = rear_snapshot.place;
      rguard.enabled = true;
      rguard.last_change_level = rear_snapshot.last_change_level;

      rguard.previous = last_rear;
      rguard.next = GREATER_IX_NULL;
      if (last_rear.second != IX32_NULL) rear_guard_at(last_rear).next = rear_snapshot.ix;
      last_rear = rear_snapshot.ix;
    }

    if (!watch_unwatch) rguard.set_watch(S);
  }

  if (snapshot.accept_depth != -2) {
    if (verbosity >= 2) {
      std::cout << "SET_ACCEPT_DEPTH_BACKJ "
        << accept_depth << " "
        << snapshot.accept_depth << " "
        << accept_level << " "
        << snapshot.accept_level << " ";
      if (snapshot.accept_place) {
        std::cout << *snapshot.accept_place << " "
          << snapshot.accept_place
          << std::endl;
      } else {
        std::cout << "N/A "
          << snapshot.accept_place
          << std::endl;
      }
    }

    accept_depth = snapshot.accept_depth;
    accept_level = snapshot.accept_level;
    accept_place = snapshot.accept_place;
  }

  --snapshot_count;

  CHECK_ALL_DUPLICATE_PLACES(*this);
}


Snapshot& Trie::new_snapshot() {
  unsigned ix = snapshot_count;
  ++snapshot_count;

  Snapshot *snapshot;
  if (ix == snapshots.size()) {
    snapshot = &snapshots.emplace_back();
  } else {
    snapshot = &snapshots[ix];
  }

  snapshot->new_rears.clear_nodestroy();
  snapshot->reasons.clear_nodestroy();
  snapshot->rear_snapshots.clear();
  snapshot->accept_depth = -2;

  return *snapshot;
}


void Place::calcReason(Solver& S, Lit p, vec<Lit>& out_reason) {
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

RearGuard& Trie::rear_guard_at(GuardIx ix) {
  if (verbosity >= 2) printf("GREATER_PLACE_AT %d %d\n", ix.first, ix.second);
  return ix.first == IX_NULL
    ? root_new_rears[ix.second]
    : snapshots[ix.first].new_rears[ix.second];
}

Reason* Trie::reset(Solver &S) {
  {
    GuardIx ix = last_rear;
    while (true) {
      if (ix.second == IX32_NULL) break;
      if (verbosity >= 2) printf("ResettingGreater %d,%d\n", ix.first, ix.second);
      RearGuard &rguard = rear_guard_at(ix);
      if (!rguard.in_conflict()) {
        rguard.remove_watch(S, rguard.get_tag());
      }
      ix = rguard.previous;
    }
  }
  root_new_rears.clear_nodestroy();
  root_reasons.clear_nodestroy();

  RearSnapshot rear_snapshot = {Place{&root, 0, IX_NULL}, GREATER_IX_FIRST, 0};
  RearGuard &root_place = root_new_rears.push_back(
    RearGuard(rear_snapshot, GREATER_IX_NULL, true)
  );

  last_rear = GREATER_IX_FIRST;

  active_var = 0;
  active_var_old = 0;

  if (verbosity >= 2) printf("RESET\n");

  if (to_cut.hor != NULL) {
    to_cut.cut_away();
    to_cut.hor = NULL;
  }

  accept_depth = -1;

  CHECK_ALL_DUPLICATE_PLACES(*this);

  return root_place.full_multimove_on_propagate(S, root_place.after_hors_change(S));
}

RearGuard::RearGuard(
  RearSnapshot rear_snapshot, GuardIx previous_
)
: WatchedPlace(rear_snapshot.place)
, ix(rear_snapshot.ix)
, last_change_level(rear_snapshot.last_change_level)
, previous(previous_)
, next(GREATER_IX_NULL)
{ }

RearGuard::RearGuard(
  RearSnapshot rear_snapshot, GuardIx previous_, bool enabled_
)
: WatchedPlace(rear_snapshot.place)
, ix(rear_snapshot.ix)
, last_change_level(rear_snapshot.last_change_level)
, previous(previous_)
, next(GREATER_IX_NULL)
, enabled(enabled_)
{ }


void RearGuard::on_accept(Solver &S) {
  enabled = false;

  Trie &trie = S.trie;
  if (previous.second != IX32_NULL) trie.rear_guard_at(previous).next = next;
  if (next.second == IX32_NULL) trie.last_rear = previous;
  else trie.rear_guard_at(next).previous = previous;

  int depth;
  int old_depth = trie.accept_depth;

  // The guard is selected for onSat whenever it is at the end of its horizontal line and
  //   - its depth is bigger than the old selected guard
  //   - or it lies on the same horizontal line (including back_ptr) as the old selected guard.
  // The latter can happen if the branch is added by onSat and it is important even if the
  // RearGuard is reused, if the level changes.
  if (is_ver()) {
    HorHead &horhead = deref_ver();
    if (horhead.hor != NULL) return;
    depth = horhead.depth;
    if (old_depth >= depth) return;
  } else if (hor == &trie.root) {
    if (old_depth > 0) return;
    if (hor->elems.size() != hor_ix + 1) return;
    depth = 0;
  } else {
    if (hor->elems.size() != hor_ix + 1) return;
    Place back = hor->back_ptr;
    depth = back.deref_ver().depth;
    if (old_depth > depth) return;
    if (old_depth == depth) {
      RearGuard *old_guard = trie.accept_place;
      if (old_guard->is_ver()) {
        if (
          old_guard->hor != back.hor ||
          old_guard->hor_ix != back.hor_ix
        ) return;
      }
      else if (old_guard->hor != hor) return;
    }
  }

  if (trie.snapshot_count != 0) {
    Snapshot &last_snapshot = trie.get_last_snapshot();
    if (last_snapshot.accept_depth == -2) {
      last_snapshot.accept_depth = old_depth;
      last_snapshot.accept_level = trie.accept_level;
      last_snapshot.accept_place = trie.accept_place;

      if (verbosity >= 2) {
        std::cout << "ACCEPT_DEPTH_BACKJ " << old_depth
          << " " << trie.accept_place
          << " " << trie.snapshot_count << std::endl;
      }
    }
  }
  if (verbosity >= 2) {
    std::cout << "SET_ACCEPT_DEPTH "
      << old_depth << " "
      << depth << " "
      << trie.accept_level << " "
      << S.decisionLevel() << " "
      << *this << " "
      << this
      << std::endl;
  }
  trie.accept_depth = depth;
  trie.accept_level = S.decisionLevel();
  trie.accept_place = this;
}


Reason* RearGuard::propagate(Solver &S, Lit p, bool& keep_watch) {
  Trie& trie = S.trie;
  if (trie.snapshot_count) {
    int level = S.decisionLevel();
    if (level != last_change_level) {
      if (verbosity >= 2) {
        std::cout << "GREATER_BACKJUMPER_ENABLE3 "
          << level << " " << last_change_level << " "
          << *this << " " << ix.first << " " << ix.second << std::endl;
      }
      CHECK_UNIQUE_REAR_SNAPSHOT(trie.get_last_snapshot(), ix);
      trie.get_last_snapshot().rear_snapshots.emplace_back(*this, ix, last_change_level);
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
    for (Place p = {hor, 0, IX_NULL}; p.hor_ix < hor->elems.size(); ++p.hor_ix) {
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
    for (Place p = {hor, 0, IX_NULL}; p.hor_ix + 1 < hor->elems.size(); ++p.hor_ix) {
      Place p2 = p;
      ++p2.hor_ix;
      file << p2 << " " << PlaceAttrs(p2, S) << "\n";
      file << p << " -- " << p2 << " [constraint=false];\n";
    }

    // Draw the vertical lines and recur into branching horizontal lines.
    for (unsigned hor_ix = 0; hor_ix < hor->elems.size(); ++hor_ix) {
      Place p1 = {hor, hor_ix, IX_NULL};
      for (Place p2 = {hor, hor_ix, 0}; p2.ver_ix < p2.deref_hor().hors.size(); ++p2.ver_ix) {
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
    ITER_LOGLIST(root_new_rears, RearGuard, x, {
      std::cout << "GREATER_PLACE -1 " << (Place &)x << " " << x.enabled << " " << x.in_conflict() << " " << &x << std::endl;
    })
    unsigned i = 0;
    for (int j = 0; j < snapshot_count; ++j) {
      Snapshot& snapshot = snapshots[j];
      ITER_LOGLIST(snapshot.new_rears, RearGuard, x, {
        std::cout << "GREATER_PLACE " << i << " " << (Place &)x << " " << x.enabled << " " << x.in_conflict() << " " << &x << std::endl;
      })
      ++i;
    }
}
