// TODO
// 2. improve code beauty
// 7. enable switching of heap vs tolerance order
// 9. test and backport posq stuff to novan
// 10. binary clause reasons implementation (it should improve performance by 10 to 20% - suspicious)

#include <algorithm>
#include <iostream>
#include <fstream>
#include <utility>

#include "Trie.h"
#include "Solver.h"

inline void check(bool expr) { assert(expr); }

int hor_head_count = 0;
int hor_count = 0;
int ver_count = 0;
RemovedWatch REMOVED_WATCH = {};
Mode TRIE_MODE = branch_always;

using std::endl;
using std::cout;

bool resetting;

#define CHECK_ALL_DUPLICATE_PLACES(trie)
#define CHECK_UNIQUE_REAR_SNAPSHOT(snapshot, ix)
#define CHECK_UNIQUE_VAN_SNAPSHOT(snapshot, ix)

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

bool Trie::add_clause(vector<Lit> &clause, Solver &S, unsigned clause_count, vector<unsigned> sharing_set) {
  vector<lbool> mask;
  mask.resize(S.nVars(), l_Undef);
  vector<Lit> preprocessed_clause;

  for (Lit lit: clause) {
    lbool sval = S.value(lit);
    if (sval == l_True) return true;
    if (sval == l_False) continue;

    lbool old_val = mask[var(lit)];
    lbool new_val = sign(lit) ? l_False : l_True;

    if (old_val == ~new_val) return true;
    if (old_val == l_Undef) {
      mask[var(lit)] = new_val;
      preprocessed_clause.push_back(lit);
    }
  }

  if (preprocessed_clause.size() == 0) return false;
  if (preprocessed_clause.size() == 1) {
    check(S.enqueue(preprocessed_clause[0]));
    return true;
  }

  if (root.elems.empty()) {
    VerHead &ver_head = root.elems.emplace_back(preprocessed_clause[0]);
    auto iter = preprocessed_clause.begin();
    ++iter;
    for (; iter != preprocessed_clause.end(); ++iter) {
      ver_head.hors.emplace_back(*iter);
    }
    return true;
  }

  Place deepest_place(&root, 0, -1);
  int max_depth = -1;

  vector<std::pair<StackItem, unsigned>> stack2;
  stack2.emplace_back(StackItem{&root, 0}, 0);

  while (!stack2.empty()) {
    auto item_and_depth = stack2.back();
    StackItem stackitem = item_and_depth.first;
    int depth = item_and_depth.second;
    Place place(stackitem.hor, stackitem.hor_ix, IX_NULL);
    stack2.pop_back();

    while (true) {
      if (place.in_exhaust()) return true;
      if (place.is_ver()) {
        HorHead &horhead = place.deref_ver();
        Lit tag = horhead.tag;
        lbool mask_val = mask[var(tag)];
        bool contained = mask_val != l_Undef && (mask_val == l_True) != sign(tag);

        if (horhead.hor == NULL) {
          if (contained) {
            ++place.ver_ix;
            ++depth;
          } else {
            if (depth > max_depth) {
              max_depth = depth;
              deepest_place = place;
            }
            break;
          }
        } else {
          if (contained) { 
            stack2.emplace_back(StackItem{horhead.hor, 0}, depth);
            ++place.ver_ix;
            ++depth;
          } else {
            place.hor = horhead.hor;
            place.hor_ix = 0;
            place.ver_ix = IX_NULL;
          }
        }

      } else {
        VerHead &verhead = place.deref_hor();
        Lit tag = verhead.tag;
        lbool mask_val = mask[var(tag)];
        bool contained = mask_val != l_Undef && (mask_val == l_False) == sign(tag);

        if (place.hor->elems.size() == place.hor_ix + 1) {
          if (contained) { 
            place.ver_ix = 0;
            ++depth;
          } else {
            if (depth > max_depth) {
              max_depth = depth;
              deepest_place = place;
            }
            break;
          }
        } else {
          if (contained) { 
            stack2.emplace_back(StackItem{place.hor, place.hor_ix + 1}, depth);
            place.ver_ix = 0;
            ++depth;
          } else {
            ++place.hor_ix;
          }
        }
      }
    }
  }

  ITER_MY_ZEROES(deepest_place, x,
    sharing_set[index(x)] = clause_count;
  )

  vector<Lit> added_vars;
  for (Lit lit: clause) {
    if (sharing_set[index(lit)] != clause_count) {
      added_vars.emplace_back(lit);
    }
  }

  if (added_vars.empty()) { deepest_place.cut_away(); return true; }

  HorLine *extended_hor;
  unsigned extended_hor_ix;

  if (deepest_place.is_ver()) {
    assert(deepest_place.deref_ver().hor == NULL);
    // We create a new horizontal empty branch right to the current final place
    // (which is vertical because least_ver_accept is set only when accepting at
    // vertical places).
    extended_hor = new HorLine{deepest_place};
    if (verbosity >= -2) ++hor_count;
    deepest_place.deref_ver().hor = extended_hor;
    extended_hor_ix = 0;
  } else {
    extended_hor = deepest_place.hor;
    extended_hor_ix = deepest_place.hor_ix + 1;
    assert(extended_hor_ix == extended_hor->elems.size());
  }

  {
    VerHead &ver_head = extended_hor->elems.emplace_back(added_vars[0]);
    auto iter = added_vars.begin();
    ++iter;
    for (; iter != added_vars.end(); ++iter) {
      ver_head.hors.emplace_back(*iter);
    }
  }

  return true;
}

inline void WatchedPlace::set_watch(Solver &S) {
  if (verbosity >= 2) {
    printf("WATCHING_TMP " L_LIT " %p\n", L_lit(get_tag()), this);
  }

  vec<Constr*> &watches = S.watches[index(~get_tag())];
#ifdef MY_DEBUG
  std::cout << std::flush; assert(watch_ix == -1);
#endif
  watch_ix = watches.size();
  if (verbosity >= 2) std::cout << "WATCH_IX_TMP " << watch_ix << " " << ~get_tag() << std::endl;
  watches.push(this);
}


void WatchedPlace::moveWatch(int i, Lit p) {
  watch_ix = i;
}

inline void WatchedPlace::remove_watch(Solver &S, Lit old_tag) {
  {
    vec<Constr*> &watches = S.watches[index(~old_tag)];
    if (verbosity >= 2) {
      std::cout << "RemoveWatchTmp " << watches.size() << " " << watch_ix << " " << ~old_tag << std::endl;
    }
#ifdef MY_DEBUG
    std::cout << std::flush; assert(watch_ix >= 0);
#endif
    if (watches.size() == watch_ix + 1) {
      watches.pop();
    } else {
      watches[watch_ix] = &REMOVED_WATCH;
    }
#ifdef MY_DEBUG
    watch_ix = -1;
#endif
  }
}


WatchedPlace::WatchedPlace(Place place)
: Place(place)
{ }

Trie::Trie()
: root{Place(NULL, 0, 0), vector<VerHead>()}
, root_new_rears()
, root_new_vans()
, snapshots()
, stack()
, root_leftmost(lit_Undef)
{ }

WhatToDo Guard::after_hors_change(Solver &S) {
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


WhatToDo Guard::after_vers_change(Solver &S) {
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


void Guard::branch(Solver &S) {
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


std::pair<Guard*, bool> StackItem::handle(Solver &S, Guard &rear, Guard *vguard) {
  Place place = {hor, hor_ix, IX_NULL};
  Trie &trie = S.trie;

  if (vguard == NULL) {
    LogList<Guard> &new_vans =
      trie.snapshot_count == 0 ? trie.root_new_vans : trie.get_last_snapshot().new_vans;

    vguard = &new_vans.emplace_back(true, place, &rear, S.decisionLevel(), false);
  } else {
    (Place &)*vguard = place;
    vguard->previous = NULL;
    vguard->next = NULL;
  }

  if (verbosity >= 2) {
    std::cout << "HANDLE_GREATER_STACK " << PlaceAttrs(place, S) << std::endl;
  }
  switch (vguard->multimove_on_propagate(S, vguard->after_hors_change(S))) {
    case MultimoveEnd::E_WATCH: {
      vguard->enabled = true;
      Guard *pre = rear.dual;
      if (pre) pre->next = vguard;
      vguard->previous = pre;
      rear.dual = vguard;
      vguard->set_watch(S);

      if (verbosity >= 2) printf("SAVE_AS_VAN_WATCH %p %d %p %p\n", hor, hor_ix, vguard, &rear);

      if (vguard->is_ver()) {
        HorLine *hor2 = vguard->deref_ver().hor;
        if (hor2 == NULL) return std::pair<Guard*, bool>(NULL, false);
        if (verbosity >= 2) {
          std::cout << "ADD_TO_GREATER_STACK3 " << PlaceAttrs(Place{hor2, 0, IX_NULL}, S) << "\n";
        }
        trie.stack.emplace_back(hor2, 0);
      } else {
        if (vguard->hor_ix + 1 == vguard->hor->elems.size()) {
          return std::pair<Guard*, bool>(NULL, false);
        }
        if (verbosity >= 2) {
          std::cout << "ADD_TO_GREATER_STACK4 " << PlaceAttrs(Place{vguard->hor, vguard->hor_ix + 1, IX_NULL}, S) << "\n";
        }
        trie.stack.emplace_back(vguard->hor, vguard->hor_ix + 1);
      }

      return std::pair<Guard*, bool>(NULL, false);
    }
    case MultimoveEnd::E_DONE: {
      if (verbosity >= 2) printf("SAVE_AS_VAN_DONE %p %d %p %p\n", hor, hor_ix, vguard, &rear);
      return std::pair<Guard*, bool>(vguard, false);
    }
    default: { // case MultimoveEnd::E_EXHAUST:
      if (resetting) { // this means that rear is an uninitialized root rear
        return std::pair<Guard*, bool>(vguard, true);
      }
      if (S.enqueue(rear.get_tag(), GClause_new(vguard))) {
        return std::pair<Guard*, bool>(NULL, false);
      } else {
        return std::pair<Guard*, bool>(vguard, true);
      }
    }
  }
}


WhatToDo Guard::move_on_propagate(Solver &S, Lit out_lit, bool do_branch) {
  if (is_ver()) {
    if (S.value(out_lit) == l_True) {
      HorLine *hor2 = deref_ver().hor;
      if (hor2 == NULL) {
        return WhatToDo::DONE;
      } else {
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
      if (hor_ix + 1 == hor->elems.size()) {
        return WhatToDo::DONE;
      }
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


MultimoveEnd Guard::multimove_on_propagate(Solver &S, WhatToDo what_to_do) {
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

Place* Guard::jump(Solver &S, Lit old_tag) {
  Trie &trie = S.trie;
  int level = S.decisionLevel();

  while (dual) {
    Guard &van = *dual;

    Lit lit = van.get_tag();
    lbool value = S.value(lit);

    if (verbosity >= 2) {
      std::cout << "JUMP_VAN "
        << this << "->" << dual
        << " " << *this << "->" << van
        << " " << lit << " " << value.toInt()
        << std::endl;
    }

    van.remove_watch(S, lit);

    if (value == l_True) {
      van.make_van_snapshot(S, S.level[var(lit)]);
      dual = van.previous;
      if (dual) dual->next = NULL;
      van.last_change_level = level;
      van.enabled = false;
      van.previous = NULL;
    } else {
      van.make_van_snapshot(S, S.decisionLevel());

      Guard *old_previous = van.previous;
      Guard *rguard = this;

      bool reuse = old_previous == NULL;

      if (reuse) {
        (Place &)*this = van;
      } else {
        LogList<Guard> &new_rears =
          trie.snapshot_count == 0 ? trie.root_new_rears : trie.get_last_snapshot().new_rears;
        rguard = van.dual = &new_rears.emplace_back(false, van, (Guard *)NULL, level, true);
        if (verbosity >= 2) {
          std::cout << "BRANCH_REAR " << rguard << " " << old_previous << " " << std::endl;
        }
        if (old_previous != NULL) old_previous->next = NULL;
        van.previous = NULL;
        rguard->dual = &van;
        dual = old_previous;
      }

      ++van.ver_ix;
      Place* conflict = van.full_multimove_on_propagate(S, van.after_vers_change(S));
      if (value == l_False) {
        if (verbosity >= 2) std::cout << "VAN_VALUE=FALSE " << rguard->dual << " " << conflict << std::endl;
        if (conflict == NULL) {
          // each branch of the pushed van will stop at a l_True or l_Undef => we recur at most once.
          // Untrue. We jump to one branch of the pushed van, we push it further, which can cause
          // unit propagation of l_False in another branch of the pushed van.
          if (verbosity >= 2) printf("JUMP2 %p\n", rguard);
          conflict = rguard->jump(S, reuse ? old_tag : lit);
          if (verbosity >= 2) printf("JUMP2END %p\n", rguard);
        }
        if (conflict != NULL) {
          // quite a heavy way to satisfy undo.remove_watch
          if (reuse) {
            if (verbosity >= 2) printf("UNTANGLE1 %p\n", rguard);
            enabled = false;
          }
          else {
            if (verbosity >= 2) printf("UNTANGLE2 %p\n", rguard);
            enabled = false;
            rguard->enabled = false;
          }
          return conflict;
        }
      } else {
        assert(conflict == NULL);
        rguard->set_watch(S);
      }
      if (reuse) {
        if (verbosity >= 2) std::cout << "SKIP_ON_ACCEPT_VAN" << std::endl;
        return NULL;
      }
    }
  }

  enabled = false;

  return NULL;
}


void Trie::undo(Solver& S) {
  if (verbosity >= 2) printf("UNDO %d %d %d %p\n", S.decisionLevel(), S.root_level, snapshot_count, &get_last_snapshot());
  Snapshot &snapshot = get_last_snapshot();

  if (verbosity >= 2) {
    std::cout << "GREATER_UNDO "
        << snapshot.new_rears.size() << "c"
        << snapshot.rear_snapshots.size() << " "
        << snapshot.new_vans.size() << "c"
        << snapshot.van_snapshots.size()
        << std::endl << std::flush;
  }

  ITER_LOGLIST(snapshot.new_vans, Guard, vguard, {
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
      vguard.untangle();
    } else if (verbosity >= 2) {
      std::cout << "SKIP_VAN " << vguard << " " << &vguard << std::endl << std::flush;
    }
  })

  ITER_LOGLIST(snapshot.new_rears, Guard, rguard, {
    if (rguard.enabled) {
      if (!rguard.in_exhaust()) {
        if (verbosity >= 2) {
          std::cout << "REMOVE_REAR " << rguard << " ";
          printf(L_LIT, L_lit(rguard.get_tag()));
          std::cout << " " << &rguard << std::endl << std::flush;
        }
      } else if (verbosity >= 2) {
        std::cout << "UNTANGLE_REAR " << rguard << " " << &rguard << std::endl << std::flush;
        assert(false);
      }

      Lit tag = rguard.get_tag();
      rguard.remove_watch(S, tag);
    } else if (verbosity >= 2) {
      std::cout << "SKIP_REAR " << rguard << " " << &rguard << std::endl << std::flush;
    }
  })

  for (VanSnapshot van_snapshot: snapshot.van_snapshots) {
    Guard &vguard = *van_snapshot.ix;

    if (verbosity >= 2) {
      std::cout << "CHANGED_VAN " << &vguard << " " << vguard << " " << van_snapshot.place
        << " " << vguard.enabled << " LCLVL "
        << vguard.last_change_level << "->" << van_snapshot.last_change_level << " "
        << vguard.dual << "->" << van_snapshot.rear
        << std::endl << std::flush;
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

      if (van_snapshot.rear != vguard.dual) {
        vguard.untangle();
        vguard.dual = van_snapshot.rear;

        Guard *last_van = vguard.dual->dual;
        vguard.previous = last_van;
        vguard.next = NULL;
        if (last_van != NULL) last_van->next = &vguard;
        vguard.dual->dual = &vguard;
      }
    } else {
      (Place &)vguard = van_snapshot.place;
      vguard.enabled = true;
      vguard.last_change_level = van_snapshot.last_change_level;
      vguard.dual = van_snapshot.rear;

      Guard *last_van = vguard.dual->dual;
      vguard.previous = last_van;
      vguard.next = NULL;
      if (last_van != NULL) last_van->next = &vguard;
      vguard.dual->dual = &vguard;
    }

    if (!watch_unwatch) vguard.set_watch(S);
  }

  for (RearSnapshot rear_snapshot: snapshot.rear_snapshots) {
    Guard &rguard = *rear_snapshot.ix;

    if (verbosity >= 2) {
      std::cout << "CHANGED_REAR " << &rguard << " " << rguard << " " << rear_snapshot.place
        << " " << rguard.enabled << " LCLVL "
        << rguard.last_change_level << "->" << rear_snapshot.last_change_level
        << "\n" << std::flush;
    }

    bool watch_unwatch = false;
    Lit new_tag = rear_snapshot.place.get_tag();

    if (rguard.enabled) {
      assert(!rguard.in_exhaust());
      Lit old_tag = rguard.get_tag();
      if (old_tag == new_tag) {
        watch_unwatch = true;
      } else {
        rguard.remove_watch(S, rguard.get_tag());
      }
      (Place &)rguard = rear_snapshot.place;
      rguard.last_change_level = rear_snapshot.last_change_level;
    } else {
      (Place &)rguard = rear_snapshot.place;
      rguard.enabled = true;
      rguard.last_change_level = rear_snapshot.last_change_level;
    }

    if (!watch_unwatch) rguard.set_watch(S);
  }

  --snapshot_count;

  if (verbosity >= 2) {std::cout << "CHECK_DUPS\n"; print_places();}
  CHECK_ALL_DUPLICATE_PLACES(*this);
}


Snapshot& Trie::new_snapshot() {
  unsigned ix = snapshot_count;
  if (verbosity >= 2) printf("NEW_SNAPSHOT %d\n", ix);
  ++snapshot_count;

  Snapshot *snapshot;
  if (ix == snapshots.size()) {
    snapshot = &snapshots.emplace_back();
  } else {
    snapshot = &snapshots[ix];
  }

  snapshot->new_rears.clear_nodestroy();
  snapshot->new_vans.clear_nodestroy();
  snapshot->rear_snapshots.clear();
  snapshot->van_snapshots.clear();
  if (verbosity >= 2) std::cout << "NEW_SNAPSHOT2 " << " " << snapshot << std::endl;

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
  ITER_LOGLIST(root_new_rears, Guard, rguard, {
    if (verbosity >= 2) printf("ResettingRear %p\n", &rguard);
    if (rguard.enabled && !rguard.in_exhaust()) rguard.remove_watch(S, rguard.get_tag());
  });

  ITER_LOGLIST(root_new_vans, Guard, vguard, {
    if (verbosity >= 2) printf("ResettingVan %p\n", &vguard);
    if (vguard.enabled && !vguard.in_exhaust()) vguard.remove_watch(S, vguard.get_tag());
  });

  root_new_rears.clear_nodestroy();
  root_new_vans.clear_nodestroy();

  Guard &root_rguard = root_new_rears.emplace_back(
    false, Place{&root, IX_NULL, IX_NULL}, (Guard *)NULL, 0, true
  );
  Guard &root_vguard = root_new_vans.emplace_back(
    true, Place{&root, 0, IX_NULL}, &root_rguard, 0, true
  );
  root_rguard.dual = &root_vguard;

  if (verbosity >= 2) printf("RESET %p %p\n", &root_rguard, &root_vguard);

  resetting = true;
  Place *conflict = root_vguard.full_multimove_on_propagate(S, root_vguard.after_hors_change(S));
  if (conflict) {
    return conflict;
  }
  resetting = false;

  return root_rguard.jump(S, lit_Undef);
}

Place* Guard::full_multimove_on_propagate(Solver &S, WhatToDo what_to_do) {
  MultimoveEnd end = multimove_on_propagate(S, what_to_do);

  Trie &trie = S.trie;
  Guard *reusable = NULL;

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
      enabled = false;
      untangle();
      reusable = this;
      break;
    }
    default: {  // MultimoveEnd::E_EXHAUST
      trie.stack.clear();
      CHECK_ALL_DUPLICATE_PLACES(trie);
      return on_exhaust(S);
    }
  }

  Guard &rear_ = *dual;
  while (!trie.stack.empty()) {
    StackItem rsi = trie.stack.back();
    trie.stack.pop_back();
    std::pair<Guard *, bool> handle_out = rsi.handle(S, rear_, reusable);
    if (handle_out.second) {
      trie.stack.clear();
      CHECK_ALL_DUPLICATE_PLACES(trie);
      return handle_out.first;
    } else reusable = handle_out.first;
  }

  CHECK_ALL_DUPLICATE_PLACES(trie);
  return NULL;
}


void Guard::make_rear_snapshot(Solver &S, int level) {
  if (last_change_level == level) return;
  if (level <= S.root_level) {last_change_level = level; return;}

  Snapshot &snapshot = S.trie.snapshots[level - S.root_level - 1];
  if (verbosity >= 2) printf("REAR_SNAPSHOT_ENABLE0 %p %p %d %d %d\n", this, hor, hor_ix, ver_ix, level);
  CHECK_UNIQUE_REAR_SNAPSHOT(snapshot, this);
  snapshot.rear_snapshots.emplace_back(
    RearSnapshot{this, *this, last_change_level}
  );
  last_change_level = level;
}

void Guard::make_van_snapshot(Solver &S, int level) {
  if (last_change_level == level) return;
  if (level <= S.root_level) {last_change_level = level; return;}

  Snapshot &snapshot = S.trie.snapshots[level - S.root_level - 1];
  if (verbosity >= 2) printf("VAN_SNAPSHOT_ENABLE0 %p %p %d %d %d\n", this, hor, hor_ix, ver_ix, level);
  CHECK_UNIQUE_VAN_SNAPSHOT(snapshot, this);
  snapshot.van_snapshots.emplace_back(VanSnapshot{this, *this, last_change_level, dual});
  last_change_level = level;
}

Place* Guard::on_exhaust(Solver &S) {
  if (resetting) { // this means that rear is an uninitialized root rear
    return this;
  }
  if (verbosity >= 2) std::cout << "ON_EXHAUST " << this << " " << dual << " " << dual->get_tag() << std::endl;
  if (S.enqueue(dual->get_tag(), GClause_new(this))) {
    return NULL;
  } else {
    return this;
  }
}


GClause Guard::propagate(Solver& S, Lit p, bool& keep_watch) {
  if (is_van) {
    if (verbosity >= 2) std::cout << "VAN_PROP " << this << " " << *this << " " << p << " " << get_tag() << std::endl;
    assert(get_tag() == ~p);

    if (!dual->enabled || S.value(dual->get_tag()) == l_True) {
      if (verbosity >= 2) std::cout << "VAN_DISABLED_REAR " << dual << std::endl;
      keep_watch = true;
      return GClause_NULL;
    }

#ifdef MY_DEBUG
    watch_ix = -1;
#endif

    if (!enabled) return GClause_NULL;

    int visit_level = last_change_level;
    make_van_snapshot(S, S.decisionLevel());

    CHECK_ALL_DUPLICATE_PLACES(S.trie);

    Lit out_lit = get_tag();
    if (verbosity >= 2) printf("OUT_LIT " L_LIT "\n", L_lit(out_lit));
    Place *confl = full_multimove_on_propagate(S, move_on_propagate(S, out_lit, false));
    if (confl == NULL) return GClause_NULL;
    else return GClause_new(confl);
  } else {
    if (verbosity >= 2) std::cout << "REAR_PROP " << this << " " << *this << " " << p << " " << last_change_level << std::endl;
    assert(get_tag() == ~p);

    make_rear_snapshot(S, S.decisionLevel());

#ifdef MY_DEBUG
    watch_ix = -1;
#endif

    Place *confl = jump(S, p);
    if (confl == NULL) return GClause_NULL;
    else return GClause_new(confl);
  }
}

void Guard::untangle() {
  if (previous != NULL) previous->next = next;
  if (next == NULL) dual->dual = previous;
  else next->previous = previous;
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
    ITER_LOGLIST(root_new_rears, Guard, x, {
      std::cout << "REAR_PLACE -1 " << (Place &)x << " " << x.enabled << " " << x.last_change_level << " ";
      if (x.enabled) std::cout << x.in_exhaust();
      else std::cout << "N/A";
      std::cout << " " << &x << std::endl;
    })
    unsigned i = 0;
    for (int j = 0; j < snapshot_count; ++j) {
      Snapshot& snapshot = snapshots[j];
      ITER_LOGLIST(snapshot.new_rears, Guard, x, {
        std::cout << "REAR_PLACE " << i << " " << (Place &)x << " " << x.enabled << " " << x.last_change_level << " ";
        if (x.enabled) std::cout << x.in_exhaust();
        else std::cout << "N/A";
        std::cout << " " << &x << std::endl;
      })
      ++i;
    }
    ITER_LOGLIST(root_new_vans, Guard, x, {
      std::cout << "VAN_PLACE -1 " << (Place &)x << " " << x.enabled << " " << x.dual << " " << x.last_change_level << " " << std::flush;
      if (x.enabled && x.dual->enabled) std::cout << x.in_exhaust();
      else std::cout << "N/A";
      std::cout << " " << &x << std::endl;
    })
    i = 0;
    for (int j = 0; j < snapshot_count; ++j) {
      Snapshot& snapshot = snapshots[j];
      ITER_LOGLIST(snapshot.new_vans, Guard, x, {
        std::cout << "VAN_PLACE " << i << " " << (Place &)x << " " << x.enabled << " " << x.dual << " " << x.last_change_level << " " << std::flush;
        if (x.enabled && x.dual->enabled) std::cout << x.in_exhaust();
        else std::cout << "N/A";
        std::cout << " " << &x << std::endl;
      })
      ++i;
    }
}
