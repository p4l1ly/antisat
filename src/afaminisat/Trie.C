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

void check_duplicate_rears(Trie &trie, RearGuard &p) {
  ITER_LOGLIST(trie.root_new_rears, RearGuard, x, {
    assert(!x.enabled || !p.enabled || &x == &p || x.hor != p.hor || x.hor_ix != p.hor_ix || x.ver_ix != p.ver_ix);
  })
  unsigned i = 0;
  for (int j = 0; j < trie.snapshot_count; ++j) {
    Snapshot& snapshot = trie.snapshots[j];
    ITER_LOGLIST(snapshot.new_rears, RearGuard, x, {
      assert(!x.enabled || !p.enabled || &x == &p || x.hor != p.hor || x.hor_ix != p.hor_ix || x.ver_ix != p.ver_ix);
    })
    ++i;
  }
}

void check_duplicate_vans(Trie &trie, VanGuard &p) {
  ITER_LOGLIST(trie.root_new_vans, VanGuard, x, {
    assert(!x.enabled || !p.enabled || &x == &p || x.hor != p.hor || x.hor_ix != p.hor_ix || x.ver_ix != p.ver_ix);
  })
  unsigned i = 0;
  for (int j = 0; j < trie.snapshot_count; ++j) {
    Snapshot& snapshot = trie.snapshots[j];
    ITER_LOGLIST(snapshot.new_vans, VanGuard, x, {
      assert(!x.enabled || !p.enabled || &x == &p || x.hor != p.hor || x.hor_ix != p.hor_ix || x.ver_ix != p.ver_ix);
    })
    ++i;
  }
}

void check_duplicate_rears_vans(Trie &trie, RearGuard &p) {
  ITER_LOGLIST(trie.root_new_vans, VanGuard, x, {
    assert(!x.enabled || !p.enabled || x.hor != p.hor || x.hor_ix != p.hor_ix || x.ver_ix != p.ver_ix);
  })
  unsigned i = 0;
  for (int j = 0; j < trie.snapshot_count; ++j) {
    Snapshot& snapshot = trie.snapshots[j];
    ITER_LOGLIST(snapshot.new_vans, VanGuard, x, {
      assert(!x.enabled || !p.enabled || x.hor != p.hor || x.hor_ix != p.hor_ix || x.ver_ix != p.ver_ix);
    })
    ++i;
  }
}

void check_all_duplicate_places(Trie &trie) {
  ITER_LOGLIST(trie.root_new_rears, RearGuard, x, {
    check_duplicate_rears(trie, x);
    check_duplicate_rears_vans(trie, x);
  })
  for (int j = 0; j < trie.snapshot_count; ++j) {
    Snapshot& snapshot = trie.snapshots[j];
    ITER_LOGLIST(snapshot.new_rears, RearGuard, x, {
      check_duplicate_rears(trie, x);
      check_duplicate_rears_vans(trie, x);
    })
  }

  ITER_LOGLIST(trie.root_new_vans, VanGuard, x, {
    check_duplicate_vans(trie, x);
  })
  for (int j = 0; j < trie.snapshot_count; ++j) {
    Snapshot& snapshot = trie.snapshots[j];
    ITER_LOGLIST(snapshot.new_vans, VanGuard, x, {
      check_duplicate_vans(trie, x);
    })
  }
}

void check_unique_rear_snapshot(Snapshot &snapshot, RearGuard *ix) {
  std::cout << std::flush;
  for (RearSnapshot &rear_snapshot: snapshot.rear_snapshots) {
    assert(rear_snapshot.ix != ix);
  }
}

void check_unique_van_snapshot(Snapshot &snapshot, VanGuard *ix) {
  std::cout << std::flush;
  for (VanSnapshot &van_snapshot: snapshot.van_snapshots) {
    assert(van_snapshot.ix != ix);
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

#ifdef MY_DEBUG
#define CHECK_UNIQUE_VAN_SNAPSHOT(snapshot, ix) check_unique_van_snapshot(snapshot, ix)
#else
#define CHECK_UNIQUE_VAN_SNAPSHOT(snapshot, ix)
#endif

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

inline bool Place::in_exhaust() const {
  return ver_ix == deref_hor().hors.size();
}

void Place::cut_away() {
  vector<HorHead> &hors = deref_hor().hors;
  if (verbosity >= 2) std::cout << "CUTTING " << *this << "\n";
  hors.erase(hors.begin() + ver_ix, hors.end());
}

inline void WatchedPlace::set_watch(Solver &S) {
  if (verbosity >= 2) {
    printf("WATCHING " L_LIT " %p\n", L_lit(get_tag()), this);
  }
  int var_ = var(get_tag());
  var_ += var_;
  {
    vec<Constr*> &watches = S.watches[var_];
#ifdef MY_DEBUG
    std::cout << std::flush; assert(watch_ix_pos == -1);
#endif
    watch_ix_pos = watches.size();
    if (verbosity >= 2) printf("WATCH_IX_POS %d %d\n", watch_ix_pos, var_ / 2);
    watches.push(this);
  }

  ++var_;
  {
    vec<Constr*> &watches = S.watches[var_];
#ifdef MY_DEBUG
    std::cout << std::flush; assert(watch_ix_neg == -1);
#endif
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
  watch_ix_pos = -1;
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
, root_new_vans()
, root_reasons()
, my_literals()
, back_ptrs()
, snapshots()
, stack()
, accepting_place(NULL, 0, 0)
, root_cuts()
{ }

bool Trie::init(const vec<Lit>& my_literals_, const unordered_set<unsigned>& init_clause_omits) {
  my_literals.reserve(my_literals_.size());
  for (int i = 0; i < my_literals_.size(); ++i) {
    my_literals.push_back(my_literals_[i]);
  }
  back_ptrs.resize(my_literals_.size());
  stack.reserve(my_literals_.size());

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
      ver_head->hors.emplace_back(my_literals[i], ++depth);
    }
  }

  return true;
}

bool Trie::guess(Solver &S) {
  CHECK_ALL_DUPLICATE_PLACES(*this);

  if (last_rear != NULL) {
    RearGuard &rguard = *last_rear;
    Lit out_lit = rguard.get_tag();
    if (verbosity >= 2) {
      std::cout << "GUESS_GREATER " << rguard << " " << &rguard << " ";
      printf(L_LIT "\n", L_lit(out_lit));
    }
    if (verbosity >= 2) std::cout << "GREATER_PUSH2 " << S.decisionLevel() << out_lit << std::endl;
#ifdef MY_DEBUG
    assert(rguard.enabled);
    assert(!rguard.in_exhaust());
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

HorHead *Place::get_leftmost() const {
  if (is_ver()) {
    return &deref_ver();
  } else {
    Place back = hor->back_ptr;
    if (back.hor == NULL) {
      return NULL;
    } else {
      return &back.deref_ver();
    }
  }
}

int Place::get_depth() const {
  if (HorHead *leftmost = get_leftmost()) return leftmost->depth;
  return 0;
}

int Place::get_depth_if_valid() const {
  if (hor == NULL) return -1;
  return get_depth();
}

void Trie::onSat(Solver &S) {
  CHECK_ALL_DUPLICATE_PLACES(*this);

  if (verbosity >= 2) {
    std::cout << "ON_SAT " << accepting_place
      << " " << S.root_level
      << " " << accepting_reusable_rear
      << " " << accepting_reusable_van
      << " " << accepting_rear_visit_level
      << " " << accepting_van_visit_level
      << " " << accepting_rear_of_van
      << " " << root_new_rears.size()
      << ":" << root_new_rears.size();
    for (int i = 0; i < snapshot_count; ++i) {
      Snapshot &snapshot = snapshots[i];
      std::cout << "," << snapshot.new_rears.size() << ":" << snapshot.new_vans.size();
    }
    std::cout << std::endl;
  }

  unordered_set<int> my_zeroes_set;

  ITER_MY_ZEROES(accepting_place, x,
      if (verbosity >= 2) {
        printf("MY_ZERO1 " L_LIT " %d %d\n", L_lit(x), S.value(x).toInt(), S.level[var(x)]);
        std::cout << std::flush;
      }
      my_zeroes_set.insert(index(x));
      assert(S.value(x) == l_False);
  )

  // max level of added_vars+my_zeroes
  int max_level = -1;

  // added_vars are (level, variable) pairs, of zero variables added in the
  // accepting condition (= not included in my_zeroes)
  vector<std::pair<int, Lit>> added_vars;
  added_vars.reserve(my_literals.size());
  for (Lit x: my_literals) {
    if (S.value(x) == l_False) {
      if (verbosity >= 2) {
        printf("MY_ZERO2 " L_LIT " %d %d\n", L_lit(x), S.value(x).toInt(), S.level[var(x)]);
      }
      int lvl = S.level[var(x)];
      if (lvl > max_level) {
        max_level = lvl;
      }
      if (!my_zeroes_set.contains(index(x))) {
        added_vars.emplace_back(lvl, x);
      }
    }
  }

  if (verbosity >= 2) printf("MAX_LEVEL %d\n", max_level);

  bool ver_accept = accepting_place.is_ver();
  // We have found a solution that covers the last traversed clause => we
  // shrink the clause (cut it up to the knee) instead of adding a new branch
  // to the trie.
  if (added_vars.size() == 0) {
    if (verbosity >= 2) printf("NO_ADDED_VAR\n");

    Place cut = ver_accept ? accepting_place : accepting_place.hor->back_ptr;
    cut.deref_ver().is_under_cut = true;
    if (accepting_van_visit_level > S.root_level) {
      snapshots[accepting_van_visit_level - S.root_level - 1].cuts.push_back(cut);
    } else {
      root_cuts.push_back(cut);
    }

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
    assert(accepting_place.deref_ver().hor == NULL);
    // We create a new horizontal empty branch right to the current final place
    // (which is vertical because least_ver_accept is set only when accepting at
    // vertical places).
    extended_hor = new HorLine{accepting_place};
    if (verbosity >= -2) ++hor_count;
    accepting_place.deref_ver().hor = extended_hor;
    extended_hor_ix = 0;
  } else {
    extended_hor = accepting_place.hor;
    extended_hor_ix = accepting_place.hor_ix + 1;
    assert(extended_hor_ix == extended_hor->elems.size());
  }

#ifdef MY_DEBUG
  {
    std::cout << std::flush;
    Lit first_lit = added_vars[0].second;
    if (ver_accept) {
      HorHead &horhead = accepting_place.deref_ver();
      assert(horhead.tag != first_lit);
    } else {
      Place back = accepting_place.hor->back_ptr;
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

  int depth = accepting_place.get_depth();

  // Add the first added_var to the current horizontal branch.
  const std::pair<int, Lit>& first_added_var = added_vars[0];
  VerHead &ver_head = extended_hor->elems.emplace_back(first_added_var.second);
  ver_head.hors.reserve(added_vars.size() - 1);
  // Continue down with a vertical branch containing the remaining added_vars.
  for (unsigned i = 1; i < added_vars.size(); ++i) {
    pair<int, Lit> added_var = added_vars[i];
    ver_head.hors.emplace_back(added_var.second, ++depth);
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
  VanGuard *vguard;

  if (accepting_reusable_rear) {
    rguard = accepting_reusable_rear;
    if (verbosity >= 2) std::cout << "REUSING_REAR " << rguard << std::endl;
  } else {
    LogList<RearGuard> *incomplete_rears;

    if (accepting_rear_visit_level <= S.root_level) incomplete_rears = &root_new_rears;
    else incomplete_rears = &snapshots[accepting_rear_visit_level - S.root_level - 1].new_rears;

    rguard = &incomplete_rears->emplace_back(
      Place{NULL, 0, 0}, 0, (RearGuard *)NULL, false, accepting_rear_of_van,
      accepting_rear_visit_level
    );
    if (verbosity >= 2) std::cout << "NEW_REAR " << rguard << std::endl;
  }

  if (accepting_reusable_van) {
    vguard = accepting_reusable_van;
    if (verbosity >= 2) std::cout << "REUSING_VAN " << vguard << std::endl;
  } else {
    LogList<VanGuard> *incomplete_vans;

    if (accepting_van_visit_level <= S.root_level) incomplete_vans = &root_new_vans;
    else incomplete_vans = &snapshots[accepting_van_visit_level - S.root_level - 1].new_vans;

    vguard = &incomplete_vans->emplace_back(Place{NULL, 0, 0}, (RearGuard *)NULL, 0, false);
    if (verbosity >= 2) std::cout << "NEW_VAN " << vguard << std::endl;
  }

  unsigned i = added_vars.size() - 1;

  bool switch_to_parent = (
    accepting_rear_of_van->fork_level > max(S.root_level, accepting_van_visit_level)
  );
  int lvl = added_vars[i].first;
  VanSnapshot *next_snapshot_van = NULL;

  {
    // if (i) --i;
    unsigned last_i_rear = i + 1;
    unsigned last_i_van = i + 2;

    if (verbosity >= 2) printf("LVLLVL %d\n", lvl);
    if (lvl < S.root_level) goto break_rear;
    RearSnapshot *next_snapshot_rear = NULL;

    for (int iter = lvl - S.root_level; iter; --lvl) {
      if (lvl <= accepting_van_visit_level) goto break_rear;
      --iter;
      Snapshot &snapshot = snapshots[iter];
      if (verbosity >= 0) printf("GLVL2 %d/%d %d\n", lvl, S.root_level, i);

      for (; i; --i) {
        const std::pair<int, Lit>& added_var = added_vars[i - 1];

        if (verbosity >= 0) printf("I %d " L_LIT " %d\n", i - 1, L_lit(added_var.second), added_var.first);

        if (added_var.first < lvl) {
          onSatSnapshots(
            i,
            last_i_rear,
            last_i_van,
            extended_hor,
            extended_hor_ix,
            lvl,
            snapshot,
            vguard,
            rguard,
            next_snapshot_van,
            next_snapshot_rear,
            added_vars,
            switch_to_parent
          );
          goto continue_rear;
        }
      }

      // If there is no added_var before the guessed variable, set its snapshot to the
      // start of the added branch.
      onSatSnapshots(
        0,
        last_i_rear,
        last_i_van,
        extended_hor,
        extended_hor_ix,
        lvl,
        snapshot,
        vguard,
        rguard,
        next_snapshot_van,
        next_snapshot_rear,
        added_vars,
        switch_to_parent
      );
      goto break_rear;
continue_rear: ;
    }
  }

break_rear: ;
  if (switch_to_parent) {
    Snapshot &snapshot = snapshots[accepting_rear_of_van->fork_level - S.root_level - 1];
    if (verbosity >= 2) {
      printf("VAN_SNAPSHOT_ENABLE4 %p %p %d %d %d\n", vguard, extended_hor, extended_hor_ix, i - 1, accepting_rear_of_van->fork_level);
    }
    CHECK_UNIQUE_VAN_SNAPSHOT(snapshot, vguard);

    RearGuard *rear_of_van = accepting_rear_of_van->parent;

    if (verbosity >= 2) {
      printf("VAN_SNAPSHOT_REAR_OF_VAN4 %p %d\n", rear_of_van, rear_of_van->fork_level);
    }

    snapshot.van_snapshots.push_back({
      vguard,
      {extended_hor, extended_hor_ix, IX_NULL},
      accepting_van_visit_level,
      rear_of_van
    });
    if (next_snapshot_van) next_snapshot_van->last_change_level = accepting_rear_of_van->fork_level;
  }


  S.cancelUntil(max_level);

  CHECK_ALL_DUPLICATE_PLACES(*this);
}


void Trie::onSatSnapshots(
  unsigned i,
  unsigned &last_i_rear,
  unsigned &last_i_van,
  HorLine *extended_hor,
  unsigned extended_hor_ix,
  int lvl,
  Snapshot &snapshot,
  VanGuard *vguard,
  RearGuard *rguard,
  VanSnapshot *&next_snapshot_van,
  RearSnapshot *&next_snapshot_rear,
  vector<std::pair<int, Lit>> &added_vars,
  bool &switch_to_parent
) {
  if (lvl <= accepting_rear_visit_level) {
    if (last_i_van > i) {
      if (verbosity >= 2) {
        printf("VAN_SNAPSHOT_ENABLE1 %p %p %d %d %d\n", vguard, extended_hor, extended_hor_ix, i - 1, lvl);
      }
      CHECK_UNIQUE_VAN_SNAPSHOT(snapshot, vguard);

      RearGuard *rear_of_van = accepting_rear_of_van;
      if (rear_of_van->fork_level >= lvl) {
        rear_of_van = rear_of_van->parent;
        switch_to_parent = false;
      }

      if (verbosity >= 2) {
        printf("VAN_SNAPSHOT_REAR_OF_VAN %p %d\n", rear_of_van, rear_of_van->fork_level);
      }

      snapshot.van_snapshots.push_back({
        vguard,
        {extended_hor, extended_hor_ix, i - 1},
        accepting_van_visit_level,
        rear_of_van
      });
      if (next_snapshot_van) next_snapshot_van->last_change_level = lvl;
      next_snapshot_van = &snapshot.van_snapshots.back();
      last_i_van = i;
    } else if (switch_to_parent) {
      RearGuard *rear_of_van = accepting_rear_of_van;
      if (rear_of_van->fork_level >= lvl) {
        switch_to_parent = false;

        if (verbosity >= 2) {
          printf("VAN_SNAPSHOT_ENABLE5 %p %p %d %d %d\n", vguard, extended_hor, extended_hor_ix, i - 1, lvl);
        }
        CHECK_UNIQUE_VAN_SNAPSHOT(snapshot, vguard);

        RearGuard *rear_of_van = accepting_rear_of_van->parent;

        if (verbosity >= 2) {
          printf("VAN_SNAPSHOT_REAR_OF_VAN5 %p %d\n", rear_of_van, rear_of_van->fork_level);
        }

        snapshot.van_snapshots.push_back({
          vguard,
          {extended_hor, extended_hor_ix, i - 1},
          accepting_van_visit_level,
          rear_of_van
        });
        if (next_snapshot_van) next_snapshot_van->last_change_level = lvl;
      }
    }
  } else {
    if (last_i_rear > i) {
      if (verbosity >= 2) {
        printf("REAR_SNAPSHOT_ENABLE2 %p %d %d %d\n", extended_hor, extended_hor_ix, i - 1, lvl);
      }
      CHECK_UNIQUE_REAR_SNAPSHOT(snapshot, rguard);

      int jumped_van_visit_level;
      if (i == 0) {
        jumped_van_visit_level = accepting_van_visit_level;
        printf("A\n");
      } else {
        int pre_level = added_vars[i - 1].first;
        if (pre_level <= accepting_van_visit_level) {
          jumped_van_visit_level = accepting_van_visit_level;
          printf("B\n");
        } else if (pre_level < accepting_rear_visit_level) {
          jumped_van_visit_level = pre_level;
          printf("C\n");
        } else if (i == 1) {
          jumped_van_visit_level = accepting_rear_visit_level;
          printf("D\n");
        } else {
          jumped_van_visit_level = added_vars[i - 2].first;
          printf("E\n");
        }
      }

      snapshot.rear_snapshots.push_back({
        rguard,
        {extended_hor, extended_hor_ix, i - 1},
        accepting_rear_visit_level,
        vguard,
        jumped_van_visit_level,
        Place(NULL, IX_NULL, 0),
        NULL,
        -1
      });
      if (next_snapshot_rear) next_snapshot_rear->last_change_level = lvl;
      next_snapshot_rear = &snapshot.rear_snapshots.back();
      last_i_rear = i;
    }

    if (i + 1 < added_vars.size() && last_i_van > i + 1) {
      if (verbosity >= 2) {
        printf("VAN_SNAPSHOT_ENABLE2 %p %p %d %d %d\n", vguard, extended_hor, extended_hor_ix, i, lvl);
      }
      CHECK_UNIQUE_VAN_SNAPSHOT(snapshot, vguard);
      snapshot.van_snapshots.push_back({
        vguard,
        {extended_hor, extended_hor_ix, i},
        accepting_van_visit_level,
        rguard
      });
      if (next_snapshot_van) next_snapshot_van->last_change_level = lvl;
      next_snapshot_van = &snapshot.van_snapshots.back();
      last_i_van = i + 1;
    }
  }
}


WhatToDo Place::after_hors_change(Solver &S) {
  Lit out = deref_hor().tag;
  if (verbosity >= 2) printf("OUTHOR " L_LIT "\n", L_lit(out));
  lbool val = S.value(out);

  if (val == l_Undef) {
    return WhatToDo::WATCH;
  }
  if (val == l_False && ver_is_singleton()) {
    ver_ix = 0;
    CHECK_ALL_DUPLICATE_PLACES(S.trie);
    return WhatToDo::EXHAUST;
  }
  return WhatToDo::AGAIN;
}


WhatToDo Place::after_vers_change(Solver &S) {
  if (in_exhaust()) return WhatToDo::EXHAUST;

  HorHead &horhead = deref_ver();

  Lit out = horhead.tag;
  if (verbosity >= 2) printf("OUTVER " L_LIT "\n", L_lit(out));
  lbool val = S.value(out);

  if (val == l_Undef) {
    return WhatToDo::WATCH;
  }
  if (val == l_False && ver_is_last()) {
    ++ver_ix;
    CHECK_ALL_DUPLICATE_PLACES(S.trie);
    return WhatToDo::EXHAUST;
  }
  return WhatToDo::AGAIN;
}


VanGuard &Place::save_as_van(Solver &S, RearGuard &rear, bool enabled) {
  Trie &trie = S.trie;

  LogList<VanGuard> &new_vans =
    trie.snapshot_count == 0 ? trie.root_new_vans : trie.get_last_snapshot().new_vans;
  VanGuard &vguard = new_vans.emplace_back(*this, &rear, S.decisionLevel(), enabled);
  if (verbosity >= 2) std::cout << "NEW_VAN1 " << &vguard << std::endl;
  if (enabled) vguard.set_watch(S);
  else vguard.on_accept(S, S.decisionLevel());
  CHECK_ALL_DUPLICATE_PLACES(trie);
  return vguard;
}


void Place::branch(Solver &S) {
  if (is_ver()) {
    HorLine *hor2 = deref_ver().hor;
    if (hor2 == NULL) return;

    if (verbosity >= 2) {
      std::cout << "ADD_TO_GREATER_STACK " << PlaceAttrs(Place{hor2, 0, IX_NULL}, S) << "\n";
    }
    S.trie.stack.emplace_back(hor2, 0);
  } else {
    if (hor_ix + 1 == hor->elems.size()) return;
    if (verbosity >= 2) {
      std::cout << "ADD_TO_GREATER_STACK2 " << PlaceAttrs(Place{hor, hor_ix + 1, IX_NULL}, S) << "\n";
    }
    S.trie.stack.emplace_back(hor, hor_ix + 1);
  }
}


Place *StackItem::handle(Solver &S, RearGuard &rear) {
  Place place = {hor, hor_ix, IX_NULL};
  if (verbosity >= 2) {
    std::cout << "HANDLE_GREATER_STACK " << PlaceAttrs(place, S) << " " << "\n";
  }
  switch (place.multimove_on_propagate(S, place.after_hors_change(S))) {
    case MultimoveEnd::E_WATCH: {
      VanGuard &vguard = place.save_as_van(S, rear);
      if (verbosity >= 2) printf("SAVE_AS_VAN_WATCH %p %d %p\n", hor, hor_ix, &vguard);

      if (place.is_ver()) {
        HorLine *hor2 = place.deref_ver().hor;
        if (hor2 == NULL) return NULL;
        S.trie.stack.emplace_back(hor2, 0);
      } else {
        if (place.hor_ix + 1 == place.hor->elems.size()) return NULL;
        S.trie.stack.emplace_back(place.hor, place.hor_ix + 1);
      }

      return NULL;
    }
    case MultimoveEnd::E_DONE: {
      VanGuard &vguard = place.save_as_van(S, rear, false);
      if (verbosity >= 2) printf("SAVE_AS_VAN_DONE %p %d %p\n", hor, hor_ix, &vguard);
      vguard.on_accept(S, S.decisionLevel());
      return NULL;
    }
    default: { // case MultimoveEnd::E_EXHAUST:
      Place *reason = S.trie.snapshot_count == 0
        ? &S.trie.root_reasons.emplace_back(place)
        : &S.trie.get_last_snapshot().reasons.emplace_back(place);
      if (rear.last_change_level == -1) { // this means that rear is an uninitialized root rear
        return reason;
      }
      if (S.enqueue(rear.get_tag(), reason)) {
        return NULL;
      } else {
        return reason;
      }
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
        if (verbosity >= 2) printf("AGAIN %d %d " L_LIT "\n", hor_ix, ver_ix, L_lit(get_tag()));
        out_lit = get_tag();
        break;
      }

      case WATCH: {
        if (verbosity >= 2) printf("WATCH %d %d " L_LIT "\n", hor_ix, ver_ix, L_lit(get_tag()));
        return MultimoveEnd::E_WATCH;
      }

      case DONE: {
        if (verbosity >= 2) printf("DONE %d %d\n", hor_ix, ver_ix);
        return MultimoveEnd::E_DONE;
      }

      case EXHAUST: {
        if (verbosity >= 2) printf("EXHAUST %d %d\n", hor_ix, ver_ix);
        return MultimoveEnd::E_EXHAUST;
      }
    }

    what_to_do = move_on_propagate(S, out_lit, true);
  }
}

Place* RearGuard::jump(Solver &S) {
  Trie &trie = S.trie;
  int level = S.decisionLevel();
  bool accepted = false;

  while (last_van) {
    VanGuard &van = *last_van;
    int van_visit_level = van.last_change_level;
    van.make_snapshot(S);

    Lit lit = van.get_tag();
    lbool value = S.value(lit);

    if (verbosity >= 2) {
      std::cout << "JUMP_VAN "
        << this << "->" << last_van
        << " " << *this << "->" << van
        << " " << lit << " " << value.toInt() << std::endl;
    }

    van.remove_watch(S, lit);

    if (value == l_True) {
      last_van = van.previous;
      van.on_accept(S, van_visit_level);
      van.last_change_level = level;
      accepted = true;
    } else {
      VanGuard *old_previous = van.previous;
      RearGuard *rguard = this;

      if (accepted || old_previous != NULL) {
        LogList<RearGuard> &new_rears =
          trie.snapshot_count == 0 ? trie.root_new_rears : trie.get_last_snapshot().new_rears;
        rguard = van.rear = &new_rears.emplace_back(van, level, trie.last_rear, enabled, this, level);
        if (trie.last_rear) trie.last_rear->next = rguard;
        trie.last_rear = rguard;
        std::cout << "BRANCH_REAR " << rguard << " " << old_previous << " " << accepted << std::endl;
        if (old_previous != NULL) old_previous->next = NULL;
        van.previous = NULL;
        rguard->last_van = &van;
        last_van = old_previous;
      } else {
        (Place &)*this = van;
      }

      rguard->jumped_van = &van;
      rguard->jumped_van_visit_level = van_visit_level;

      ++van.ver_ix;
      Place* conflict = van.full_multimove_on_propagate(S, van.after_vers_change(S));
      if (value == l_False) {
        if (conflict == NULL) {
          // each branch of the pushed van will stop at a l_True or l_Undef => we recur at most once.
          conflict = rguard->jump(S);
          if (conflict != NULL) {(Place &)*this = (Place &)*rguard = *conflict; return conflict;}
        } else {(Place&)*this = (Place &)*rguard = *conflict; return conflict;}
      } else {
        assert(conflict == NULL);
        rguard->set_watch(S);
      }
      if (!accepted && old_previous == NULL) {return NULL;}
    }
  }

  on_accept_van(S);

  return NULL;
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
        << snapshot.new_rears.size() << "c"
        << snapshot.rear_snapshots.size() << " "
        << snapshot.new_vans.size() << "c"
        << snapshot.van_snapshots.size()
        << std::endl << std::flush;
  }

  ITER_LOGLIST(snapshot.new_vans, VanGuard, vguard, {
    if (vguard.enabled) {
      if (!vguard.in_exhaust()) {
        if (verbosity >= 2) {
          std::cout << "REMOVE_VAN " << vguard << " ";
          printf(L_LIT, L_lit(vguard.get_tag()));
          std::cout << " " << &vguard << std::endl << std::flush;
        }
        vguard.remove_watch(S, vguard.get_tag());
      } else if (verbosity >= 2) {
        std::cout << "UNTANGLE_VAN " << vguard << " " << &vguard << std::endl << std::flush;
      }

      vguard.enabled = false;
      if (vguard.previous != NULL) vguard.previous->next = vguard.next;
      if (vguard.next == NULL) vguard.rear->last_van = vguard.previous;
      else vguard.next->previous = vguard.previous;
    } else if (verbosity >= 2) {
      std::cout << "SKIP_VAN " << vguard << " " << &vguard << std::endl << std::flush;
    }
  })

  ITER_LOGLIST(snapshot.new_rears, RearGuard, rguard, {
    if (rguard.enabled) {
      if (!rguard.in_exhaust()) {
        if (verbosity >= 2) {
          std::cout << "REMOVE_REAR " << rguard << " ";
          printf(L_LIT, L_lit(rguard.get_tag()));
          std::cout << " " << &rguard << std::endl << std::flush;
        }
        rguard.remove_watch(S, rguard.get_tag());
      } else if (verbosity >= 2) {
        std::cout << "UNTANGLE_REAR " << rguard << " " << &rguard << std::endl << std::flush;
      }

      rguard.enabled = false;
      if (rguard.previous != NULL) rguard.previous->next = rguard.next;
      if (rguard.next == NULL) last_rear = rguard.previous;
      else rguard.next->previous = rguard.previous;
    } else if (verbosity >= 2) {
      std::cout << "SKIP_REAR " << rguard << " " << &rguard << std::endl << std::flush;
    }
  })

  for (VanSnapshot van_snapshot: snapshot.van_snapshots) {
    VanGuard &vguard = *van_snapshot.ix;

    if (verbosity >= 2) {
      std::cout << "CHANGED_VAN " << &vguard << " " << vguard << " " << van_snapshot.place
        << " " << vguard.enabled << " LCLVL "
        << vguard.last_change_level << "->" << van_snapshot.last_change_level
        << std::endl << std::flush;
    }

    if (HorHead *leftmost = van_snapshot.place.get_leftmost()) {
      if (leftmost->is_under_cut) {
        std::cout << "IS_UNDER_CUT" << std::endl;
        continue;
      }
    }

    bool watch_unwatch = false;
    Lit new_tag = van_snapshot.place.get_tag();

    if (vguard.enabled) {
      if (!vguard.in_exhaust()) {
        Lit old_tag = vguard.get_tag();
        if (old_tag == new_tag) {
          watch_unwatch = true;
        } else {
          vguard.remove_watch(S, vguard.get_tag());
        }
      }
      (Place &)vguard = van_snapshot.place;
      vguard.last_change_level = van_snapshot.last_change_level;

      if (van_snapshot.rear != vguard.rear) {
        if (vguard.previous != NULL) vguard.previous->next = vguard.next;
        if (vguard.next == NULL) vguard.rear->last_van = vguard.previous;
        else vguard.next->previous = vguard.previous;

        vguard.rear = van_snapshot.rear;

        VanGuard *last_van = vguard.rear->last_van;
        vguard.previous = last_van;
        vguard.next = NULL;
        if (last_van != NULL) last_van->next = &vguard;
        vguard.rear->last_van = &vguard;
      }
    } else {
      (Place &)vguard = van_snapshot.place;
      vguard.enabled = true;
      vguard.last_change_level = van_snapshot.last_change_level;
      vguard.rear = van_snapshot.rear;

      VanGuard *last_van = vguard.rear->last_van;
      vguard.previous = last_van;
      vguard.next = NULL;
      if (last_van != NULL) last_van->next = &vguard;
      vguard.rear->last_van = &vguard;
    }

    if (!watch_unwatch) vguard.set_watch(S);
  }

  for (RearSnapshot rear_snapshot: snapshot.rear_snapshots) {
    RearGuard &rguard = *rear_snapshot.ix;

    if (verbosity >= 2) {
      std::cout << "CHANGED_REAR " << &rguard << " " << rguard << " " << rear_snapshot.place
        << " " << rguard.enabled << " LCLVL "
        << rguard.last_change_level << "->" << rear_snapshot.last_change_level
        << "\n" << std::flush;
    }

    bool watch_unwatch = false;
    Lit new_tag = rear_snapshot.place.get_tag();

    if (rguard.enabled) {
      if (!rguard.in_exhaust()) {
        Lit old_tag = rguard.get_tag();
        if (old_tag == new_tag) {
          watch_unwatch = true;
        } else {
          rguard.remove_watch(S, rguard.get_tag());
        }
      }
      (Place &)rguard = rear_snapshot.place;
      rguard.last_change_level = rear_snapshot.last_change_level;
      rguard.jumped_van = rear_snapshot.jumped_van;
      rguard.jumped_van_visit_level = rear_snapshot.jumped_van_visit_level;
      rguard.accepting_place = rear_snapshot.accepting_place;
      rguard.accepting_reusable_van = rear_snapshot.accepting_reusable_van;
      rguard.accepting_van_visit_level = rear_snapshot.accepting_van_visit_level;
    } else {
      (Place &)rguard = rear_snapshot.place;
      rguard.enabled = true;
      rguard.last_change_level = rear_snapshot.last_change_level;
      rguard.jumped_van = rear_snapshot.jumped_van;
      rguard.jumped_van_visit_level = rear_snapshot.jumped_van_visit_level;
      rguard.accepting_place = rear_snapshot.accepting_place;
      rguard.accepting_reusable_van = rear_snapshot.accepting_reusable_van;
      rguard.accepting_van_visit_level = rear_snapshot.accepting_van_visit_level;

      rguard.previous = last_rear;
      rguard.next = NULL;
      if (last_rear != NULL) last_rear->next = rear_snapshot.ix;
      last_rear = rear_snapshot.ix;
    }

    if (!watch_unwatch) rguard.set_watch(S);
  }

  if (snapshot.accepting_place.hor_ix != IX_NULL) {
    if (verbosity >= 2) {
      std::cout << "SET_ACCEPT_DEPTH_BACKJ "
        << accepting_place << "->"
        << snapshot.accepting_place << " "
        << accepting_reusable_rear << "->"
        << snapshot.accepting_reusable_rear << " "
        << accepting_reusable_van << "->"
        << snapshot.accepting_reusable_van << " "
        << accepting_rear_visit_level << "->"
        << snapshot.accepting_rear_visit_level << " "
        << accepting_van_visit_level << "->"
        << snapshot.accepting_van_visit_level << " "
        << accepting_rear_of_van << "->"
        << snapshot.accepting_rear_of_van
        << std::endl;
    }

    accepting_place = snapshot.accepting_place;
    accepting_reusable_rear = snapshot.accepting_reusable_rear;
    accepting_reusable_van = snapshot.accepting_reusable_van;
    accepting_rear_visit_level = snapshot.accepting_rear_visit_level;
    accepting_van_visit_level = snapshot.accepting_van_visit_level;
    accepting_rear_of_van = snapshot.accepting_rear_of_van;
  }

  for (Place cut : snapshot.cuts) cut.cut_away();

  --snapshot_count;


  if (verbosity >= 2) {std::cout << "CHECK_DUPS\n"; print_places();}
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
  snapshot->new_vans.clear_nodestroy();
  snapshot->reasons.clear_nodestroy();
  snapshot->rear_snapshots.clear();
  snapshot->van_snapshots.clear();
  snapshot->cuts.clear();
  snapshot->accepting_place = Place(NULL, IX_NULL, 0);

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
      std::cout << "CALC_REASON_EXHAUST " << *this;
      ITER_MY_ZEROES(*this, x, printf(" " L_LIT, L_lit(x));)
      printf("\n");
    }

    S.cancelUntil(max_level);
  }
  else {
    ITER_MY_ZEROES(*this, x,
      if (S.value(x) == l_False) {
        out_reason.push(~x);
      } else {
        assert(x == p);
      }
    )

    if (verbosity >= 2) {
      printf("CALC_REASON_PLACE " L_LIT " ", L_lit(p));
      std::cout << *this;
      ITER_MY_ZEROES(*this, x,
          printf(" " L_LIT ":%d", L_lit(x), S.value(x).toInt());
      )
      printf("\n");
    }
  }
}

Place* Trie::reset(Solver &S) {
  {
    RearGuard *rguard = last_rear;
    while (true) {
      if (rguard == NULL) break;
      if (verbosity >= 2) printf("ResettingRear %p\n", rguard);
      if (!rguard->in_exhaust()) {
        rguard->remove_watch(S, rguard->get_tag());
      }
      rguard = rguard->previous;
    }
  }

  ITER_LOGLIST(root_new_vans, VanGuard, vguard, {
    if (verbosity >= 2) printf("ResettingVan %p\n", &vguard);
    if (vguard.enabled && !vguard.in_exhaust()) vguard.remove_watch(S, vguard.get_tag());
  });

  for (Place cut : root_cuts) cut.cut_away();
  root_cuts.clear();

  root_new_rears.clear_nodestroy();
  root_new_vans.clear_nodestroy();
  root_reasons.clear_nodestroy();

  RearGuard &root_rguard = root_new_rears.emplace_back(
    Place{&root, IX_NULL, IX_NULL}, -1, (RearGuard *)NULL, true, (RearGuard *)NULL, -1
  );
  VanGuard &root_vguard = root_new_vans.emplace_back(
    Place{&root, 0, IX_NULL}, &root_rguard, 0, true
  );

  active_var = 0;
  active_var_old = 0;

  if (verbosity >= 2) printf("RESET %p %p\n", &root_rguard, &root_vguard);

  accepting_place.hor = NULL;

  Place *conflict = root_vguard.full_multimove_on_propagate(S, root_vguard.after_hors_change(S));
  if (conflict) {
    last_rear = NULL;
    return conflict;
  }
  root_rguard.last_change_level = 0;
  last_rear = &root_rguard;
  return root_rguard.jump(S);
}

Place* VanGuard::full_multimove_on_propagate(Solver &S, WhatToDo what_to_do) {
  MultimoveEnd end = multimove_on_propagate(S, what_to_do);

  Trie &trie = S.trie;

  switch (end) {
    case MultimoveEnd::E_WATCH: {
      set_watch(S);
      if (is_ver()) {
        HorLine *hor2 = deref_ver().hor;
        if (hor2 == NULL) break;
        trie.stack.emplace_back(hor2, 0);
      } else {
        if (hor_ix + 1 == hor->elems.size()) break;
        trie.stack.emplace_back(hor, hor_ix + 1);
      }
      break;
    }
    case MultimoveEnd::E_DONE: {
      on_accept(S, S.decisionLevel());
      break;
    }
    default: {  // MultimoveEnd::E_EXHAUST
      trie.stack.clear();
      CHECK_ALL_DUPLICATE_PLACES(trie);
      return on_exhaust(S);
    }
  }

  RearGuard &rear_ = *rear;
  while (!trie.stack.empty()) {
    StackItem rsi = trie.stack.back();
    trie.stack.pop_back();
    Place *reason = rsi.handle(S, rear_);
    if (reason != NULL) {
      trie.stack.clear();
      CHECK_ALL_DUPLICATE_PLACES(trie);
      return reason;
    }
  }

  CHECK_ALL_DUPLICATE_PLACES(trie);
  return NULL;
}


void VanGuard::on_accept(Solver &S, int visit_level) {
  if (verbosity >= 2) {
    std::cout << "ON_ACCEPT " << this << " " << rear << " " << previous << " " << next << " "
      << last_change_level << " " << S.decisionLevel() << " " << rear->last_change_level << std::endl;
  }
  enabled = false;
  if (previous != NULL) previous->next = next;
  if (next == NULL) rear->last_van = previous;
  else next->previous = previous;

  Trie &trie = S.trie;
  int global_depth;
  int rear_depth;
  int depth;

  // The guard is selected for onSat whenever it is at the end of its horizontal line and
  //   - its depth is bigger than the old selected guard
  //   - or it lies on the same horizontal line (including back_ptr) as the old selected guard.
  // The latter can happen if the branch is added by onSat and it is important even if the
  // RearGuard is reused, if the level changes.
  if (is_ver()) {
    HorHead &horhead = deref_ver();
    if (horhead.hor != NULL) return;
    depth = horhead.depth;
    global_depth = trie.accepting_place.get_depth_if_valid();
    if (global_depth >= depth) return;
    rear_depth = rear->accepting_place.get_depth_if_valid();
    if (rear_depth >= depth) return;
  } else if (hor == &trie.root) {
    global_depth = trie.accepting_place.get_depth_if_valid();
    if (global_depth > 0) return;
    if (hor->elems.size() != hor_ix + 1) return;
    rear_depth = rear->accepting_place.get_depth_if_valid();
    if (rear_depth > 0) return;
    depth = 0;
  } else {
    if (hor->elems.size() != hor_ix + 1) return;
    Place back = hor->back_ptr;
    depth = back.deref_ver().depth;
    global_depth = trie.accepting_place.get_depth_if_valid();
    if (global_depth > depth) return;
    rear_depth = rear->accepting_place.get_depth_if_valid();
    if (rear_depth > depth) return;

    if (global_depth == depth && rear_depth == depth) {
      Place old_accepting_place = rear->accepting_place;
      if (old_accepting_place.is_ver()) {
        if (
          old_accepting_place.hor != back.hor ||
          old_accepting_place.hor_ix != back.hor_ix
        ) return;
      }
      else if (old_accepting_place.hor != hor) return;
    }
  }

  rear->make_snapshot(S);

  printf("DEEPEST_VAN_ACCEPT\n");

  rear->accepting_van_visit_level = visit_level;
  if (visit_level == S.decisionLevel()) rear->accepting_reusable_van = this;
  else rear->accepting_reusable_van = NULL;
  rear->accepting_place = *this;
}

void RearGuard::make_snapshot(Solver &S) {
  int level = S.decisionLevel();
  if (last_change_level == level) return;
  if (level <= S.root_level) {last_change_level = level; return;}

  Snapshot &snapshot = S.trie.get_last_snapshot();
  CHECK_UNIQUE_REAR_SNAPSHOT(snapshot, this);
  snapshot.rear_snapshots.emplace_back(
    RearSnapshot{
      this, *this, last_change_level, jumped_van, jumped_van_visit_level, accepting_place,
      accepting_reusable_van, accepting_van_visit_level
    }
  );
  last_change_level = level;
}

void VanGuard::make_snapshot(Solver &S) {
  int level = S.decisionLevel();
  if (last_change_level == level) return;
  if (level <= S.root_level) {last_change_level = level; return;}

  Snapshot &snapshot = S.trie.get_last_snapshot();
  CHECK_UNIQUE_VAN_SNAPSHOT(snapshot, this);
  printf("VAN_SNAPSHOT_ENABLE0 %p %p %d %d %d\n", this, hor, hor_ix, ver_ix, level);
  snapshot.van_snapshots.emplace_back(VanSnapshot{this, *this, last_change_level, rear});
  last_change_level = level;
}


Place* VanGuard::on_exhaust(Solver &S) {
  if (rear->last_change_level == -1) { // this means that rear is an uninitialized root rear
    return this;
  }
  if (verbosity >= 2) std::cout << "ON_EXHAUST " << this << " " << rear << " " << rear->get_tag() << std::endl;
  if (S.enqueue(rear->get_tag(), this)) {
    return NULL;
  } else {
    return this;
  }
}


Reason* VanGuard::propagate(Solver& S, Lit p, bool& keep_watch) {
  if (verbosity >= 2) std::cout << "VAN_PROP " << this << " " << *this << " " << p << " " << get_tag() << std::endl;
  assert(get_tag() == p || get_tag() == ~p);

  if (!rear->enabled) {
    if (verbosity >= 2) std::cout << "VAN_DISABLED_REAR " << rear << std::endl;
    keep_watch = true;
    return NULL;
  }

  if (sign(p)) {
#ifdef MY_DEBUG
    watch_ix_neg = -1;
#endif
    remove_watch_pos(S, ~p);
  } else {
#ifdef MY_DEBUG
    watch_ix_pos = -1;
#endif
    remove_watch_neg(S, ~p);
  }

  if (!enabled) return NULL;

  int visit_level = last_change_level;
  make_snapshot(S);

  Trie& trie = S.trie;

  Lit out_lit = get_tag();

  lbool value = S.value(out_lit);

  if (value == l_True) {
    if (verbosity >= 2) std::cout << "TRIGGERED_VAN_ACCEPT" << std::endl;
    on_accept(S, visit_level);
    CHECK_ALL_DUPLICATE_PLACES(trie);
    return NULL;
  }

  if (verbosity >= 2) printf("OUT_LIT " L_LIT "\n", L_lit(out_lit));
  CHECK_ALL_DUPLICATE_PLACES(trie);
  return full_multimove_on_propagate(S, move_on_propagate(S, out_lit, false));
}


void Trie::make_accepting_snapshot(Solver &S) {
  int level = S.decisionLevel();
  if (level <= S.root_level) return;
  Snapshot &snapshot = get_last_snapshot();
  if (snapshot.accepting_place.hor_ix != IX_NULL) return;

  snapshot.accepting_place = accepting_place;
  snapshot.accepting_reusable_rear = accepting_reusable_rear;
  snapshot.accepting_reusable_van = accepting_reusable_van;
  snapshot.accepting_rear_visit_level = accepting_rear_visit_level;
  snapshot.accepting_van_visit_level = accepting_van_visit_level;
  snapshot.accepting_rear_of_van = accepting_rear_of_van;

  if (verbosity >= 2) {
    std::cout << "MAKE_ACCEPTING_SNAPSHOT "
      << snapshot.accepting_place << " "
      << snapshot.accepting_reusable_rear << " "
      << snapshot.accepting_reusable_van << " "
      << snapshot.accepting_rear_visit_level << " "
      << snapshot.accepting_van_visit_level << " "
      << snapshot.accepting_rear_of_van
      << std::endl;
  }
}


void RearGuard::on_accept_van(Solver &S) {
  if (verbosity >= 2) std::cout << "ON_ACCEPT_VAN " << this << " " << *this << " " << accepting_place << std::endl;

  enabled = false;
  Trie &trie = S.trie;
  if (previous != NULL) previous->next = next;
  if (next == NULL) trie.last_rear = previous;
  else next->previous = previous;

  int global_depth;
  int depth;

  // The guard is selected for onSat whenever it is at the end of its horizontal line and
  //   - its depth is bigger than the old selected guard
  //   - or it lies on the same horizontal line (including back_ptr) as the old selected guard.
  // The latter can happen if the branch is added by onSat and it is important even if the
  // RearGuard is reused, if the level changes.
  if (accepting_place.hor == NULL) return;
  if (accepting_place.is_ver()) {
    HorHead &horhead = accepting_place.deref_ver();
    if (horhead.hor != NULL) return;
    depth = horhead.depth;
    global_depth = trie.accepting_place.get_depth_if_valid();
    if (global_depth >= depth) return;
  } else if (accepting_place.hor == &trie.root) {
    global_depth = trie.accepting_place.get_depth_if_valid();
    if (global_depth > 0) return;
    if (accepting_place.hor->elems.size() != accepting_place.hor_ix + 1) return;
    depth = 0;
  } else {
    if (accepting_place.hor->elems.size() != accepting_place.hor_ix + 1) return;
    Place back = accepting_place.hor->back_ptr;
    depth = back.deref_ver().depth;
    global_depth = trie.accepting_place.get_depth_if_valid();
    if (global_depth > depth) return;

    if (global_depth == depth) {
      Place old_accepting_place = trie.accepting_place;
      if (old_accepting_place.is_ver()) {
        if (
          old_accepting_place.hor != back.hor ||
          old_accepting_place.hor_ix != back.hor_ix
        ) return;
      }
      else if (old_accepting_place.hor != accepting_place.hor) return;
    }
  }

  trie.make_accepting_snapshot(S);

  std::cout << "DEEPEST_ACCEPT\n";
  trie.accepting_place = accepting_place;
  trie.accepting_van_visit_level = accepting_van_visit_level;
  trie.accepting_rear_of_van = this;
  int level = S.decisionLevel();
  trie.accepting_rear_visit_level = level;
  if (accepting_van_visit_level == level) trie.accepting_reusable_van = accepting_reusable_van;
  else trie.accepting_reusable_van = NULL;
  trie.accepting_reusable_rear = this;
  return;
}


void RearGuard::on_accept_rear(Solver &S, int visit_level) {
  enabled = false;
  Trie &trie = S.trie;
  if (previous != NULL) previous->next = next;
  if (next == NULL) trie.last_rear = previous;
  else next->previous = previous;

  int global_depth;
  int depth;

  // The guard is selected for onSat whenever it is at the end of its horizontal line and
  //   - its depth is bigger than the old selected guard
  //   - or it lies on the same horizontal line (including back_ptr) as the old selected guard.
  // The latter can happen if the branch is added by onSat and it is important even if the
  // RearGuard is reused, if the level changes.

  if (is_ver()) {
    HorHead &horhead = deref_ver();
    if (horhead.hor != NULL) return;
    depth = horhead.depth;
    global_depth = trie.accepting_place.get_depth_if_valid();
    if (global_depth >= depth) return;
  } else if (hor == &trie.root) {
    global_depth = trie.accepting_place.get_depth_if_valid();
    if (global_depth > 0) return;
    if (hor->elems.size() != hor_ix + 1) return;
    depth = 0;
  } else {
    if (hor->elems.size() != hor_ix + 1) return;
    Place back = hor->back_ptr;
    depth = back.deref_ver().depth;
    global_depth = trie.accepting_place.get_depth_if_valid();
    if (global_depth > depth) return;

    if (global_depth == depth) {
      Place old_accepting_place = trie.accepting_place;
      if (old_accepting_place.is_ver()) {
        if (
          old_accepting_place.hor != back.hor ||
          old_accepting_place.hor_ix != back.hor_ix
        ) return;
      }
      else if (old_accepting_place.hor != hor) return;
    }
  }

  trie.make_accepting_snapshot(S);

  std::cout << "DEEPEST_ACCEPT " << jumped_van_visit_level << " " << visit_level << std::endl;
  trie.accepting_place = *this;
  trie.accepting_van_visit_level = jumped_van_visit_level;
  trie.accepting_rear_visit_level = visit_level;
  int level = S.decisionLevel();
  if (jumped_van_visit_level == level) trie.accepting_reusable_van = jumped_van;
  else trie.accepting_reusable_van = NULL;
  if (visit_level == level) {
    trie.accepting_reusable_rear = this;
  }
  else {
    trie.accepting_reusable_rear = NULL;
  }
  trie.accepting_rear_of_van = this;
}


Reason* RearGuard::propagate(Solver &S, Lit p, bool& keep_watch) {
  if (verbosity >= 2) std::cout << "REAR_PROP " << this << " " << *this << " " << p << " " << last_change_level << std::endl;
  assert(get_tag() == p || get_tag() == ~p);

  int visit_level = last_change_level;
  make_snapshot(S);

  if (sign(p)) {
#ifdef MY_DEBUG
    watch_ix_neg = -1;
#endif
    remove_watch_pos(S, ~p);
  } else {
#ifdef MY_DEBUG
    watch_ix_pos = -1;
#endif
    remove_watch_neg(S, ~p);
  }

  Lit out_lit = get_tag();
  lbool value = S.value(out_lit);

  if (value == l_True) {
    if (verbosity >= 2) std::cout << "TRIGGERED_REAR_ACCEPT " << this << std::endl;
    on_accept_rear(S, visit_level);

    CHECK_ALL_DUPLICATE_PLACES(S.trie);
    return NULL;
  }

  return jump(S);
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
      std::cout << "REAR_PLACE -1 " << (Place &)x << " " << x.enabled << " " << x.last_change_level << " ";
      if (x.enabled) std::cout << x.in_exhaust();
      else std::cout << "N/A";
      std::cout << " " << &x << std::endl;
    })
    unsigned i = 0;
    for (int j = 0; j < snapshot_count; ++j) {
      Snapshot& snapshot = snapshots[j];
      ITER_LOGLIST(snapshot.new_rears, RearGuard, x, {
        std::cout << "REAR_PLACE " << i << " " << (Place &)x << " " << x.enabled << " " << x.last_change_level << " ";
        if (x.enabled) std::cout << x.in_exhaust();
        else std::cout << "N/A";
        std::cout << " " << &x << std::endl;
      })
      ++i;
    }
    ITER_LOGLIST(root_new_vans, VanGuard, x, {
      std::cout << "VAN_PLACE -1 " << (Place &)x << " " << x.enabled << " " << x.rear << " " << x.last_change_level << " " << std::flush;
      if (x.enabled && x.rear->enabled) std::cout << x.in_exhaust();
      else std::cout << "N/A";
      std::cout << " " << &x << std::endl;
    })
    i = 0;
    for (int j = 0; j < snapshot_count; ++j) {
      Snapshot& snapshot = snapshots[j];
      ITER_LOGLIST(snapshot.new_vans, VanGuard, x, {
        std::cout << "VAN_PLACE " << i << " " << (Place &)x << " " << x.enabled << " " << x.rear << " " << x.last_change_level << " " << std::flush;
        if (x.enabled && x.rear->enabled) std::cout << x.in_exhaust();
        else std::cout << "N/A";
        std::cout << " " << &x << std::endl;
      })
      ++i;
    }
}
