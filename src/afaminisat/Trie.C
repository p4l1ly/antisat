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

using std::endl;
using std::cout;

bool Trie::add_clause(
    vector<Lit> &clause,
    Solver &S,
    unsigned clause_count,
    vector<unsigned> sharing_set,
    vector<Horline> &horlines,
    vector<Head*> &verlines
) {
  vec<char> mask;
  mask.growTo(S.nVars(), 0);
  vector<Lit> preprocessed_clause;

  for (Lit lit: clause) {
    lbool sval = S.value(lit);
    if (sval == l_True) return true;
    if (sval == l_False) continue;

    char old_val = mask[var(lit)];
    char new_val = sign(lit) ? 1 : -1;

    if (old_val == -new_val) return true;
    if (old_val == 0) {
      mask[var(lit)] = new_val;
      preprocessed_clause.push_back(lit);
    }
  }

  if (preprocessed_clause.size() == 0) return false;
  if (preprocessed_clause.size() == 1) {
    check(S.enqueue(preprocessed_clause[0]));
    return true;
  }

  if (root == NULL) {
    Horline &horline = horlines.emplace_back(&root, (Head*)NULL);
    Head &verhead = horline.elems.emplace_back(preprocessed_clause[0]);

    unsigned depth = 0;
    root = &verhead;

    Head *verline = verlines.emplace_back(new Head[preprocessed_clause.size() - 1]);

    Head *above = &verhead;
    for (unsigned i = 1; i != preprocessed_clause.size(); ++i) {
      Head &horhead = verline[i - 1];
      horhead.tag = preprocessed_clause[i];
      horhead.above = above;

      if (i == 1) verhead.dual_next = &horhead;
      else above->next = &horhead;

      horhead.depth = ++depth;

      above = &horhead;
    }
    return true;
  }

  Head *deepest_place;
  int max_depth = -1;

  MultimoveCtx ctx(mask);
  pair<Head*, MultimoveEnd> move = ctx.first(pair(root, ctx.after_right(root)));

  while (move.first != NULL) {
    switch (move.second) {
      case MultimoveEnd::E_EXHAUST: return true;
      default: {
        if ((int)move.first->depth > max_depth) {
          if (move.first->is_ver) {
            if (move.first->dual_next != NULL) break;
          } else {
            if (move.first->next != NULL) break;
          }
          if (verbosity >= 2) cout << "MAX_DEPTH " << move.first->depth << endl;
          max_depth = move.first->depth;
          deepest_place = move.first;
        }
      }
    }
    move = ctx.next();
  }

  {
    Head *zero_iter = deepest_place;
    while (true) {
      if (zero_iter->is_ver) zero_iter = zero_iter->above;
      else zero_iter = horlines[zero_iter->external].above;

      if (zero_iter == NULL) break;
      sharing_set[index(zero_iter->tag)] = clause_count;
    }
  }

  vector<Lit> added_vars;
  for (Lit lit: preprocessed_clause) {
    if (sharing_set[index(lit)] != clause_count) {
      added_vars.emplace_back(lit);
    }
  }

  if (added_vars.empty()) {
    Head *above = deepest_place;
    if (above->is_ver) above = above->above;
    else above = horlines[above->external].above;

    if (above->is_ver) above->next = NULL;
    else above->dual_next = NULL;

    return true;
  }

  {
    Head *verheadptr;
    int horline_ix;

    if (deepest_place->is_ver) {
      horline_ix = horlines.size();
      deepest_place->external = horline_ix;
      Horline &horline = horlines.emplace_back(&deepest_place->dual_next, deepest_place->above);
      verheadptr = &horline.elems.emplace_back(added_vars[0]);
    } else {
      horline_ix = deepest_place->external;
      Horline &horline = horlines[horline_ix];
      Head *ptr0 = &horline.elems[0];
      verheadptr = &horline.elems.emplace_back(added_vars[0]);

      Head *next;
      if ((next = &horline.elems[0]) != ptr0) {
        deepest_place = verheadptr;
        --deepest_place;

        *horline.ptr_to_first = next;

        while(true) {
          Head *dual_next = next->dual_next;
          if (dual_next != NULL) {
            dual_next->above = next;
            if (dual_next->dual_next != NULL) horlines[dual_next->external].above = next;
          }
          Head *prev = next++;
          if (next == verheadptr) break;
          prev->next = next;
        }
      }
    }
    Head &verhead = *verheadptr;

    verhead.next = NULL;
    verhead.external = horline_ix;
    unsigned depth = verhead.depth = deepest_place->depth;
    if (deepest_place->is_ver) deepest_place->dual_next = verheadptr;
    else deepest_place->next = verheadptr;

    Head *verline = verlines.emplace_back(new Head[added_vars.size() - 1]);

    Head *above = verheadptr;
    for (unsigned i = 1; i != added_vars.size(); ++i) {
      Head &horhead = verline[i - 1];
      horhead.tag = added_vars[i];
      horhead.above = above;

      if (i == 1) verhead.dual_next = &horhead;
      else above->next = &horhead;

      horhead.depth = ++depth;
      above = &horhead;
    }
  }
  return true;
}

inline void Head::set_watch(Solver &S) {
  if (watching) return;

  if (verbosity >= 2) cout << "WATCHING " << HeadAttrs(this, S) << endl;

  vec<Constr*> &watches = S.watches[index(~tag)];

  watching = true;
  watches.push(this);
}


WhatToDo MultimoveCtx::after_right(Head *x) {
  Lit tag = x->tag;
  char val = assigns[var(tag)];
  if (verbosity >= 2) cout << "AFTER_RIGHT " << *x << " " << (int)val << endl;

  if (val == 0) return WhatToDo::WATCH;
  if ((val == 1) != sign(tag)) return WhatToDo::RIGHT_HOR;
  if (x->dual_next == NULL) return WhatToDo::EXHAUST;
  return WhatToDo::DOWN_HOR;
}

WhatToDo MultimoveCtx::after_down(Head *x) {
  Lit tag = x->tag;
  char val = assigns[var(tag)];
  if (verbosity >= 2) cout << "AFTER_DOWN " << *x << " " << (int)val << endl;

  if (val == 0) return WhatToDo::WATCH;
  if ((val == 1) != sign(tag)) return WhatToDo::RIGHT_VER;
  if (x->next == NULL) return WhatToDo::EXHAUST;
  return WhatToDo::DOWN_VER;
}

void MultimoveCtx::branch_ver(Head *x) {
  Head *nxt = x->dual_next;
  if (nxt == NULL) return;
  if (verbosity >= 2) std::cout << "BRANCH_VER " << *nxt << endl;
  stack.emplace_back(nxt, after_right(nxt));
}

void MultimoveCtx::branch_hor(Head *x) {
  Head *nxt = x->next;
  if (nxt == NULL) return;
  if (verbosity >= 2) std::cout << "BRANCH_HOR " << *nxt << endl;
  stack.emplace_back(nxt, after_right(nxt));
}

pair<Head *, WhatToDo> MultimoveCtx::move_down_ver(Head *x) {
  Head *nxt = x->next;
  if (nxt == NULL) return pair(x, WhatToDo::EXHAUST);
  return pair(nxt, after_down(nxt));
}

pair<Head *, WhatToDo> MultimoveCtx::move_down_hor(Head *x) {
  Head *nxt = x->dual_next;
  if (nxt == NULL) return pair(x, WhatToDo::EXHAUST);
  return pair(nxt, after_down(nxt));
}

pair<Head *, WhatToDo> MultimoveCtx::move_right_ver(Head *x) {
  Head *nxt = x->dual_next;
  if (nxt == NULL) return pair(x, WhatToDo::DONE);
  return pair(nxt, after_right(nxt));
}

pair<Head *, WhatToDo> MultimoveCtx::move_right_hor(Head *x) {
  Head *nxt = x->next;
  if (nxt == NULL) return pair(x, WhatToDo::DONE);
  return pair(nxt, after_right(nxt));
}

pair<Head *, WhatToDo> MultimoveCtx::move_right(Head *x) {
  return x->is_ver ? move_right_ver(x) : move_right_hor(x);
}

pair<Head *, WhatToDo> MultimoveCtx::move_down(Head *x) {
  return x->is_ver ? move_down_ver(x) : move_down_hor(x);
}

pair<Head *, MultimoveEnd> MultimoveCtx::multimove(pair<Head*, WhatToDo> move) {
  while (true) {
    switch (move.second) {
      case RIGHT_VER: {
        if (verbosity >= 2) cout << "RIGHT_VER " << *move.first << endl;
        move = move_right_ver(move.first);
        continue;
      }

      case RIGHT_HOR: {
        if (verbosity >= 2) cout << "RIGHT_HOR " << *move.first << endl;
        move = move_right_hor(move.first);
        continue;
      }

      case DOWN_VER: {
        if (verbosity >= 2) cout << "DOWN_VER " << *move.first << endl;
        branch_ver(move.first);
        move = move_down_ver(move.first);
        continue;
      }

      case DOWN_HOR: {
        if (verbosity >= 2) cout << "DOWN_HOR " << *move.first << endl;
        branch_hor(move.first);
        move = move_down_hor(move.first);
        continue;
      }

      case WATCH: {
        if (verbosity >= 2) cout << "WATCH " << *move.first << endl;
        return pair(move.first, MultimoveEnd::E_WATCH);
      }

      case DONE: {
        if (verbosity >= 2) cout << "DONE " << *move.first << endl;
        return pair(move.first, MultimoveEnd::E_DONE);
      }

      case EXHAUST: {
        if (verbosity >= 2) cout << "EXHAUST " << *move.first << endl;
        return pair(move.first, MultimoveEnd::E_EXHAUST);
      }
    }
  }
}

pair<Head *, MultimoveEnd> MultimoveCtx::first(pair<Head*, WhatToDo> move) {
  pair<Head *, MultimoveEnd> result = multimove(move);
  switch (result.second) {
    case MultimoveEnd::E_WATCH: {
      Head *y = result.first;
      Head *nxt = y->is_ver ? y->dual_next : y->next;
      if (nxt != NULL) stack.emplace_back(nxt, after_right(nxt));
      return result;
    }
    case MultimoveEnd::E_EXHAUST: stack.clear();
    default: return result;
  }
}

pair<Head *, MultimoveEnd> MultimoveCtx::next() {
  if (stack.empty()) return pair((Head*)NULL, MultimoveEnd::E_DONE);
  auto move = stack.back();
  stack.pop_back();
  return first(move);
}

pair<Head *, MultimoveEnd> MultimoveCtx::first_solo(pair<Head*, WhatToDo> move, Solver &S) {
again:
  pair<Head *, MultimoveEnd> result = multimove(move);
  switch (result.second) {
    case MultimoveEnd::E_WATCH: {
      Head *y = result.first;
      Head *nxt;
      Head *below;
      if (y->is_ver) {
        nxt = y->dual_next;
        below = y->next;
      } else {
        nxt = y->next;
        below = y->dual_next;
      }

      if (below == NULL) {
        check(S.enqueue(y->tag, GClause_new(y)));
        if (nxt == NULL) return pair(y, MultimoveEnd::E_DONE);
        move = pair(nxt, after_right(nxt));
        goto again;
      }

      if (nxt != NULL) stack.emplace_back(nxt, after_right(nxt));
      return result;
    }
    case MultimoveEnd::E_EXHAUST: stack.clear();
    default: return result;
  }
}

pair<Head *, MultimoveEnd> MultimoveCtx::next_solo(Solver &S) {
  if (stack.empty()) return pair((Head*)NULL, MultimoveEnd::E_DONE);
  auto move = stack.back();
  stack.pop_back();
  return first_solo(move, S);
}

MinusSnapshot *Head::save_to_msnap(Trie &trie, MinusSnapshot *msnap) {
  if (verbosity >= 2) {
    cout << "SAVE_TO_MSNAP"
      << " " << msnap
      << " " << *this
      << " " << trie.snapshot_count
      << " " << guard.dual
      << endl;
  }
  if (msnap == NULL) {
    if (trie.snapshot_count == 0) return &trie.root_minus_snapshots.emplace_back(this);
    return &trie.get_last_snapshot().minus_snapshots.emplace_back(this);
  }
  msnap->place = this;
  return msnap;
}

Head* Head::full_multimove_on_propagate(
  Solver &S,
  WhatToDo what_to_do,
  MinusSnapshot *msnap,  // NULL if a reusable snapshot does not exist.
  Head *rear,  // its dual should be initialized, otherwise only the place is relevant.
  Head *gprev,
  Head *gnext
) {
  Trie &trie = S.trie;
  int level = S.decisionLevel();

  bool found_watch = false;
  pair<Head*, MultimoveEnd> move = trie.multimove_ctx.first(pair(this, what_to_do));
  while (move.first != NULL) {
    Head *x = move.first;
    switch (move.second) {
      case MultimoveEnd::E_WATCH: {
        x->guard.init(VAN_GUARD, rear, level, x->save_to_msnap(trie, msnap));
        msnap = NULL;

        if (found_watch) {
          // Tangle a new place
          Head *prev = rear->guard.dual;
          if (prev) prev->guard.next = x;
          x->guard.previous = prev;
          x->guard.next = NULL;
          rear->guard.dual = x;
        } else {
          // Replace the tangled original place.
          if (gprev) gprev->guard.next = x;
          if (gnext) gnext->guard.previous = x;
          else rear->guard.dual = x;
          x->guard.previous = gprev;
          x->guard.next = gnext;
          found_watch = true;
        }

        x->set_watch(S);
        break;
      }
      case MultimoveEnd::E_DONE:
#ifdef AFA
        if (x->right() == NULL) {
          if (
            rear->guard.deepest_rightmost_van == NULL ||
            rear->guard.deepest_rightmost_van->right() ||
            x->depth > rear->guard.deepest_rightmost_van->depth
          ) {
            rear->guard.deepest_rightmost_van = x;
          }
        }
#endif
        break;
      case MultimoveEnd::E_EXHAUST:
        if (verbosity >= 2) {
          cout << "ON_EXHAUST"
            << " " << HeadAttrs(x, S)
            << " " << HeadAttrs(rear, S)
            << endl;
        }

        if (!found_watch) {
          if (msnap) msnap->place = NULL;
          if (gprev) gprev->guard.next = gnext;
          if (gnext) gnext->guard.previous = gprev;
          else rear->guard.dual = gprev;
        }

        if (S.enqueue(rear->tag, GClause_new(x))) return NULL;
        return x;
    }
    move = trie.multimove_ctx.next();
  }

  if (!found_watch) {
    // Everything is DONE, untangle the original place.
    if (msnap) msnap->place = NULL;
    if (gprev) gprev->guard.next = gnext;
    if (gnext) gnext->guard.previous = gprev;
    else rear->guard.dual = gprev;
  }

  return NULL;
}

Head* Head::full_multimove_on_propagate_solo(
  Solver &S,
  WhatToDo what_to_do,
  MinusSnapshot *msnap  // NULL if a reusable snapshot does not exist.
) {
  Trie &trie = S.trie;
  int level = S.decisionLevel();

  pair<Head*, MultimoveEnd> move = trie.multimove_ctx.first_solo(pair(this, what_to_do), S);
  while (move.first != NULL) {
    Head *x = move.first;
    switch (move.second) {
      case MultimoveEnd::E_WATCH: {
        x->guard.init(SOLO_GUARD, NULL, level, x->save_to_msnap(trie, msnap));
        msnap = NULL;
        x->set_watch(S);

        S.watch_on(x->tag);

#ifdef AFA
        trie.deepest_rightmost_candidate(x);
#endif

        break;
      }
      case MultimoveEnd::E_DONE:
#ifdef AFA
        trie.deepest_rightmost_candidate(x);
#endif
        break;
      case MultimoveEnd::E_EXHAUST:
        if (verbosity >= 2) cout << "ON_EXHAUST_SOLO " << HeadAttrs(x, S) << endl;
        if (msnap) {
          if (verbosity >= 2) printf("CLEAR_MSNAP\n");
          msnap->place = NULL;
        }
        return x;
    }
    move = trie.multimove_ctx.next_solo(S);
  }

  if (msnap) {
    if (verbosity >= 2) printf("CLEAR_MSNAP\n");
    msnap->place = NULL;
  }
  return NULL;
}

#ifdef AFA
void Trie::deepest_rightmost_candidate(Head *rear) {
  if (rear->right() == NULL) {
    if (
      deepest_rightmost_rear->right() ||
      rear->depth > deepest_rightmost_rear->depth
    ) {
      deepest_rightmost_rear = rear;
    }
  }
}
#endif

Head* Head::jump(Solver &S) {
  Trie &trie = S.trie;
  int level = S.decisionLevel();

  MinusSnapshot *msnap =
    guard.last_change_level == S.decisionLevel() ? guard.minus_snapshot : NULL;
  Head *vanptr = guard.dual;

  while (vanptr) {
    Head &van = *vanptr;
    assert(van.guard.next == NULL);

    Lit lit = van.tag;
    lbool value = S.value(lit);

    if (verbosity >= 2) {
      std::cout << "JUMP_VAN "
        << HeadAttrs(this, S) << " -> " << HeadAttrs(vanptr, S)
        << " " << van.guard.previous
        << std::endl;
    }

    guard.dual = vanptr = van.guard.previous;
    if (vanptr) {
      assert(vanptr->guard.next == &van);
      vanptr->guard.next = NULL;
    }

    if (value == l_True) {
      if (van.guard.last_change_level == level) van.guard.minus_snapshot->place = NULL;
      van.make_van_psnap(S, S.level[var(lit)]);
      van.guard.guard_type = DANGLING_GUARD;
#ifdef AFA
      trie.deepest_rightmost_candidate(&van);
#endif
    } else {
      MinusSnapshot *van_msnap =
        van.guard.last_change_level == level ? van.guard.minus_snapshot : NULL;
      van.make_van_psnap(S, S.decisionLevel());

      pair<Head*, WhatToDo> move = trie.multimove_ctx.move_down(&van);
      if (move.second == WhatToDo::EXHAUST) {
        if (verbosity >= 2) cout << "SHORT_EXHAUST " << move.first << endl;
        if (van_msnap) van_msnap->place = NULL;
        van.guard.guard_type = DANGLING_GUARD;
        if (msnap) msnap->place = NULL;
        if (!S.enqueue(lit, GClause_new(move.first))) return move.first;
#ifdef AFA
        trie.deepest_rightmost_candidate(&van);
#endif
      } else {
        Head *van2 = move.first;
        van.guard.dual = van2;
#ifdef AFA
        van.guard.deepest_rightmost_van = NULL;
#endif
        Head* conflict = van2->full_multimove_on_propagate(
          S, move.second, van_msnap, &van, NULL, NULL
        );
        if (conflict != NULL) {
          if (msnap) msnap->place = NULL;
          van.guard.guard_type = DANGLING_GUARD;
          return conflict;
        }

        van.guard.guard_type = REAR_GUARD;
        van.guard.last_change_level = level;
        van.guard.minus_snapshot = van.save_to_msnap(trie, msnap);
        msnap = NULL;

        S.watch_on(lit);
#ifdef AFA
        trie.deepest_rightmost_candidate(&van);
#endif
      }
    }
  }

  // All vans have accepted. We have an empty van list, we don't watch, nor continue anywhere =>
  // we remove the msnap.
  if (msnap) msnap->place = NULL;
#ifdef AFA
  if (guard.deepest_rightmost_van) trie.deepest_rightmost_candidate(guard.deepest_rightmost_van);
#endif

  return NULL;
}

void Guard::untangle() {
  guard_type = DANGLING_GUARD;
  if (previous != NULL) previous->guard.next = next;
  if (next == NULL) dual->guard.dual = previous;
  else next->guard.previous = previous;
}

void MinusSnapshot::undo(Solver &S) {
  if (place != NULL) {
    Guard &guard = place->guard;
    if (verbosity >= 2) {
      cout << "UNDO_MINUS"
        << " " << HeadAttrs(place, S)
        << " " << guard.dual
        << " " << guard.previous
        << " " << guard.next
        << endl;
    }
    assert(place->watching);
    switch (guard.guard_type) {
    case VAN_GUARD: guard.untangle(); break;
    case REAR_GUARD:
    case SOLO_GUARD:
      S.watch_off(place->tag);
    default:;
    }
    guard.guard_type = DANGLING_GUARD;
  }
}

void Trie::undo(Solver& S) {
  Snapshot &snapshot = get_last_snapshot();

  if (verbosity >= 2) {
    cout << "UNDO"
      << " " << S.decisionLevel()
      << " " << S.root_level
      << " " << snapshot_count
      << " " << &snapshot
      << " " << snapshot.plus_snapshots.size()
      << " " << snapshot.minus_snapshots.size()
      << endl << std::flush;
  }

  ITER_LOGLIST_BACK(snapshot.minus_snapshots, MinusSnapshot, msnap, {
    msnap.undo(S);
  })

  ITER_LOGLIST_BACK(snapshot.plus_snapshots, PlusSnapshot, psnap, {
    if (verbosity >= 2) {
      cout << "UNDO_PLUS" << " " << HeadAttrs(psnap.place, S);
      if (psnap.dual == NULL) cout << " " << "R";
      else {
        cout << " " << HeadAttrs(psnap.dual, S) << " / " << psnap.dual->guard.dual;
      }
      cout
        << " " << psnap.last_change_level
        << " " << psnap.minus_snapshot
        << endl;
    }

    Head *place = psnap.place;
    Guard &guard = place->guard;
    if (psnap.dual == NULL) {
      assert(guard.guard_type == REAR_GUARD || guard.guard_type == SOLO_GUARD);
      S.watch_on(place->tag);
#ifdef AFA
      deepest_rightmost_rear = psnap.deepest_rightmost_guard;
#endif
    } else {
      assert(psnap.dual->watching);
      assert(psnap.dual->guard.guard_type == REAR_GUARD);

      guard.guard_type = VAN_GUARD;
      guard.dual = psnap.dual;
#ifdef AFA
      guard.dual->guard.deepest_rightmost_van = psnap.deepest_rightmost_guard;
#endif

      guard.previous = psnap.dual->guard.dual;
      if (guard.previous) guard.previous->guard.next = place;
      guard.next = NULL;
      psnap.dual->guard.dual = place;
    }
    guard.minus_snapshot = psnap.minus_snapshot;
    guard.last_change_level = psnap.last_change_level;

    place->set_watch(S);
  })

  --snapshot_count;
}

Snapshot& Trie::new_snapshot() {
  unsigned ix = snapshot_count;
  if (verbosity >= 2) printf("NEW_SNAPSHOT %d\n", ix);
  ++snapshot_count;

  Snapshot *snapshot = ix == snapshots.size() ? &snapshots.emplace_back() : &snapshots[ix];

  snapshot->plus_snapshots.clear_nodestroy();
  snapshot->minus_snapshots.clear_nodestroy();
  if (verbosity >= 2) std::cout << "NEW_SNAPSHOT2 " << " " << snapshot << std::endl;

  return *snapshot;
}


void Head::calcReason(Solver& S, Lit p, vec<Lit>& out_reason) {
  if (p == lit_Undef) {
    Head *iter = this;
    if (verbosity >= 2) std::cout << "CALC_REASON_EXHAUST " << HeadAttrs(this, S) << endl;

    out_reason.grow(depth + 1);
    while (iter) {
      out_reason.push(~iter->tag);
      if (verbosity >= 2) std::cout << "REASON_EXHAUST " << HeadAttrs(iter, S) << endl;
#ifdef AFA
      if (iter->is_ver) iter = iter->above;
      else iter = iter->above == NULL ? NULL : iter->above->above;
#else
      iter = iter->above;
#endif
    }
  }
  else {
    Head *iter = this;
    if (verbosity >= 2) std::cout << "CALC_REASON_PLACE " << HeadAttrs(this, S) << endl;

    out_reason.grow(depth);
    while (iter) {
      Lit lit = iter->tag;
      if (lit != p) out_reason.push(~lit);
      assert((S.value(lit) == l_False) == (lit != p));
      if (verbosity >= 2) std::cout << "REASON_PLACE " << HeadAttrs(iter, S) << endl;
#ifdef AFA
      if (iter->is_ver) iter = iter->above;
      else iter = iter->above == NULL ? NULL : iter->above->above;
#else
      iter = iter->above;
#endif
    }
  }
}

void Head::make_rear_psnap(Solver &S) {
  int level = S.decisionLevel();
  if (guard.last_change_level == level) return;
  if (level <= S.root_level) {guard.last_change_level = level; return;}

  Snapshot &snapshot = S.trie.snapshots[level - S.root_level - 1];
  if (verbosity >= 2) {
    cout << "MAKE_REAR_PSNAP " << level << " " << HeadAttrs(this, S) << endl;
  }

  snapshot.plus_snapshots.emplace_back(
    this, guard.last_change_level, (Head*)NULL, guard.minus_snapshot
#ifdef AFA
    , S.trie.deepest_rightmost_rear
#endif
  );
  guard.last_change_level = level;
}

void Head::make_van_psnap(Solver &S, int level) {
  if (guard.last_change_level == level) return;
  if (level <= S.root_level) {guard.last_change_level = level; return;}

  Snapshot &snapshot = S.trie.snapshots[level - S.root_level - 1];
  if (verbosity >= 2) {
    cout << "MAKE_VAN_PSNAP " << level << " " << HeadAttrs(this, S) << endl;
  }
  snapshot.plus_snapshots.emplace_back(
    this, guard.last_change_level, guard.dual, guard.minus_snapshot
#ifdef AFA
    , guard.dual->guard.deepest_rightmost_van
#endif
  );
  guard.last_change_level = level;
}

GClause Head::propagate(Solver& S, Lit p, bool& keep_watch) {
  assert(tag == ~p);
  assert(watching);

  switch (guard.guard_type) {
    case DANGLING_GUARD: {
      watching = false;
      return GClause_NULL;
    }

    case VAN_GUARD: {
      if (verbosity >= 2) {
        cout << "VAN_PROP"
          << " " << HeadAttrs(this, S)
          << " " << guard.previous
          << " " << guard.next
          << " " << guard.dual;
        if (guard.dual) cout << " " << guard.dual->guard.dual;
        cout << endl;
      }
      assert(guard.dual->guard.dual != NULL);
      if (guard.next == NULL) assert(guard.dual->guard.dual == this);

      if (S.value(guard.dual->tag) == l_True) {
        if (verbosity >= 2) cout << "VAN_DISABLED_REAR " << HeadAttrs(guard.dual, S) << endl;
        keep_watch = true;
        return GClause_NULL;
      }

      watching = false;

      int level = S.decisionLevel();
      MinusSnapshot *msnap = guard.last_change_level == level ? guard.minus_snapshot : NULL;
      make_van_psnap(S, level);

      pair<Head*, WhatToDo> move = S.trie.multimove_ctx.move_down(this);
      Head *confl = move.first->full_multimove_on_propagate(
        S,
        move.second,
        msnap,
        guard.dual,
        guard.previous,
        guard.next
      );
      if (confl == NULL) return GClause_NULL;
      else return GClause_new(confl);
    }

    case REAR_GUARD: {
      if (verbosity >= 2) cout << "REAR_PROP " << HeadAttrs(this, S) << endl;
      watching = false;

      S.watch_off(tag);

      Head *confl = jump(S);
      make_rear_psnap(S);
      if (confl == NULL) return GClause_NULL;
      else return GClause_new(confl);
    }

    case SOLO_GUARD: {
      if (verbosity >= 2) {
        cout << "SOLO_PROP" << " " << HeadAttrs(this, S) << endl;
      }

      S.watch_off(tag);

      watching = false;

      int level = S.decisionLevel();
      MinusSnapshot *msnap = guard.last_change_level == level ? guard.minus_snapshot : NULL;
      make_rear_psnap(S);

      pair<Head*, WhatToDo> move = S.trie.multimove_ctx.move_down(this);
      Head *confl = move.first->full_multimove_on_propagate_solo(S, move.second, msnap);
      if (confl == NULL) return GClause_NULL;
      else return GClause_new(confl);
    }
  }

  assert(false);
  return GClause_NULL;
}

Head* Trie::reset(Solver &S) {
  ITER_LOGLIST_BACK(root_minus_snapshots, MinusSnapshot, msnap, {
    msnap.undo(S);
  });
  root_minus_snapshots.clear_nodestroy();

#ifdef ALL_SOLO
  root->full_multimove_on_propagate_solo(S, multimove_ctx.after_right(root), NULL);
#else
  pair<Head*, WhatToDo> move0 = pair(root, multimove_ctx2.after_right(root));
  pair<Head*, MultimoveEnd> move = multimove_ctx2.first(move0);
  while (move.first != NULL) {
    Head *vanptr = move.first;
    switch (move.second) {
      case MultimoveEnd::E_WATCH: {
        if (verbosity >= 2) cout << "RESET_MOVE_DOWN " << HeadAttrs(vanptr, S) << endl;
        Head &van = *vanptr;
        pair<Head*, WhatToDo> move2 = multimove_ctx.move_down(vanptr);
        if (move2.second == WhatToDo::EXHAUST) {
          if (!S.enqueue(van.tag, GClause_new(vanptr))) {
            multimove_ctx2.stack.clear();
            return vanptr;
          }
        } else {
          Head *van2 = move2.first;
          van.guard.dual = van2;
#ifdef AFA
          van.guard.deepest_rightmost_van = NULL;
#endif
          Head* conflict = van2->full_multimove_on_propagate(
            S, move2.second, NULL, vanptr, NULL, NULL
          );
          if (conflict != NULL) {
            multimove_ctx2.stack.clear();
            return conflict;
          }

          van.guard.guard_type = REAR_GUARD;
          van.guard.last_change_level = 0;
          van.guard.minus_snapshot = van.save_to_msnap(*this, NULL);

          S.watch_on(van.tag);
          van.set_watch(S);
        }

        break;
      }
      case MultimoveEnd::E_DONE: {
#ifdef AFA
        if (vanptr->right() == NULL) {
          if (vanptr->depth > deepest_rightmost_rear->depth) {
            deepest_rightmost_rear = vanptr;
          }
        }
#endif
        break;
      }
      case MultimoveEnd::E_EXHAUST: return vanptr;
    }

    move = multimove_ctx2.next();
  }
#endif

  return NULL;
}

unsigned Head::count() {
  unsigned result = 0;

  vector<pair<Head*, Head*>> stack;
  stack.emplace_back((Head*)NULL, this);

  while (!stack.empty()) {
    pair<Head*, Head*> horline = stack.back();
    stack.pop_back();

    for (Head *verhead = horline.second; verhead; verhead = verhead->next) {
      ++result;
      for (Head *horhead2 = verhead->dual_next; horhead2; horhead2 = horhead2->next) {
        ++result;
        if (horhead2->dual_next != NULL) stack.emplace_back(horhead2, horhead2->dual_next);
      }
    }
  }

  return result;
}

Head* Head::solidify() {
  unsigned cnt = count();
  Head *whole_mem = new Head[cnt];
  Head *mem = whole_mem;

  vector<pair<Head*, Head*>> stack;
  stack.emplace_back((Head*)NULL, this);

  while (!stack.empty()) {
    pair<Head*, Head*> horline = stack.back();
    stack.pop_back();

    if (horline.first) horline.first->dual_next = mem;

    Head *bef_hor = NULL;
    for (Head *verhead = horline.second; verhead; verhead = verhead->next) {
      new(mem) Head(std::move(*verhead));
      if (mem->above) mem->above = horline.first->above;
      if (bef_hor != NULL) bef_hor->next = mem;
      bef_hor = mem;

      if (mem->dual_next != NULL) mem->dual_next = mem + 1;
      ++mem;

      for (Head *horhead = verhead->dual_next; horhead; horhead = horhead->next) {
        new(mem) Head(std::move(*horhead));
        mem->above = mem - 1;

        if (horhead->dual_next != NULL) stack.emplace_back(mem, horhead->dual_next);

        if (mem->next) mem->next = mem + 1;
        ++mem;
      }
    }
  }

  return whole_mem;
}

unsigned Trie::count() {
  if (root == NULL) return 0;
  else return root->count();
}

Head* Trie::solidify() {
  if (root == NULL) return NULL;
  else {
    Head *solid = root->solidify();
    root = &solid[0];
    return solid;
  }
}

void Trie::to_dot(Solver& S, const char *filename) {
  std::ofstream file;
  file.open(filename);
  file << "strict graph {\n";

  vector<pair<Head*, Head*>> stack;
  if (root != NULL) stack.emplace_back((Head*)NULL, root);

  while (!stack.empty()) {
    pair<Head*, Head*> horline = stack.back();
    stack.pop_back();

    // Pose the line horizontally.
    file << "subgraph { rank=same";
    if (horline.first) file << "; \"" << horline.first << '"';
    for (Head *verhead = horline.second; verhead; verhead = verhead->next) {
      file << "; \"" << verhead << '"';
    }
    file << " };\n";

    // Connect the horizontal line and make it infinitely flexible.
    file << DotHead(horline.second, S) << ";\n";
    if (horline.first) {
      file << '"' << horline.first << "\" -- \"" << horline.second << "\" [constraint=false];\n";
    }

    for (Head *verhead = horline.second; verhead; verhead = verhead->next) {
      if (verhead->next == NULL) break;
      file << DotHead(verhead->next, S) << ";\n";
      file << '"' << verhead << "\" -- \"" << verhead->next << "\" [constraint=false];\n";
    }

    // Draw the vertical lines and recur into branching horizontal lines.
    for (Head *verhead = horline.second; verhead; verhead = verhead->next) {
      for (Head *horhead2 = verhead->dual_next; horhead2; horhead2 = horhead2->next) {
        file << DotHead(horhead2, S) << ";\n";
        file << '"' << horhead2->above << "\" -- \"" << horhead2 << "\";\n";
        if (horhead2->dual_next != NULL) {
          stack.emplace_back(horhead2, horhead2->dual_next);
        }
      }
    }
  }

  file << "}\n";
  file.close();
}

std::ostream& operator<<(std::ostream& os, Head const &p) {
  std::string guard_type;
  switch (p.guard.guard_type) {
    case REAR_GUARD: guard_type = "R"; break;
    case VAN_GUARD: guard_type = "V"; break;
    case DANGLING_GUARD: guard_type = "∅"; break;
  }

  return os
    << &p
    << ":" << (sign(p.tag) ? "~" : "") << var(p.tag)
    << (p.is_ver ? "↓" : "→" )
    << p.depth
    << (p.watching ? "+" : "-")
    << guard_type
    << p.guard.last_change_level
    // << "^" << p.guard.dual
    ;
}

std::ostream& operator<<(std::ostream& os, HeadAttrs const &p) {
  return os << *p.head << '=' << p.S.value(p.head->tag).toInt();
}

std::ostream& operator<<(std::ostream& os, DotHead const &p) {
  return os << '"' << p.head << "\" ["
    << "label=\"" << (sign(p.head->tag) ? "~" : "") << var(p.head->tag) << "\""
    << ",tooltip=\"" << HeadAttrs(p.head, p.S) << "\""
    // TODO colors by guard_type, watching, S.value
    << "]";
}

void Trie::print_guards(Solver &S) {
  ITER_LOGLIST(root_minus_snapshots, MinusSnapshot, x, {
    if (x.place->watching && x.place->guard.guard_type != DANGLING_GUARD)
      std::cout << "GUARD -1 " << HeadAttrs(x.place, S) << endl;
  })
  for (int i = 0; i < snapshot_count; ++i) {
    Snapshot& snapshot = snapshots[i];
    ITER_LOGLIST(snapshot.minus_snapshots, MinusSnapshot, x, {
      if (x.place->watching && x.place->guard.guard_type != DANGLING_GUARD)
        std::cout << "GUARD " << i << ' ' << HeadAttrs(x.place, S) << endl;
    })
  }
}
