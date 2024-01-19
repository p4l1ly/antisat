#include <math.h>
#include "VarOrder.h"
#include "Solver.h"

inline void check(bool expr) { assert(expr); }

unsigned global_bubble_move_count = 0;
unsigned global_bubble_move_count_undo = 0;


void VarOrder::undo(Solver &S) {
  if (verbosity >= 2) {
    std::cout << "VARORDER_UNDO"
      << " " << guess_line
      << " " << snapshots.back()
      << " " << snapshots.size() - 1
      << " " << order.size()
      << " " << (guess_line == order.size() ? -2 : barriers[guess_line])
      << " " << S.decisionLevel()
      << std::endl;
  }

#ifdef MY_DEBUG
  for (int i = 0; snapshots.back() != -1 && i < snapshots.back(); ++i) {
    if (S.assigns[order[i]] == 0) { printf("NOOO %d %d\n", i, order[i]); assert(false); }
  }
#endif

  if (isinf(tolerance)) {
    guess_line = snapshots.back();
    return;
  }

  unsigned bubble_move_count = 0;
  unsigned this_max_bubble_moves = max_bubble_moves;

  if (guess_line != -1 && guess_line != order.size()) {
    assert(barriers[guess_line] != -1 && barriers[guess_line] < S.decisionLevel());
    if (barriers[guess_line] == S.decisionLevel() - 1) barriers[guess_line] = -1;
  }

  int right_ix = guess_line;

  guess_line = snapshots.back();
  snapshots.pop_back();

  assert(
    guess_line == -1 || guess_line == order.size() || barriers[guess_line] != -1 &&
    barriers[guess_line] < S.decisionLevel() - 1
  );

  for (; right_ix != order.size(); ++right_ix) {
    if (update0(order[right_ix], right_ix, S) == 0) break;
  }

#ifdef MY_DEBUG
  for (int i = 0; guess_line != -1 && i < guess_line; ++i) {
    if (S.assigns[order[i]] == 0) { printf("NOOO %d %d\n", i, order[i]); assert(false); }
  }
#endif
}


bool VarOrder::select(Solver &S)
{
    if (verbosity >= -3) printf("VARORDER_SELECT %d\n", guess_line);

#ifdef MY_DEBUG
    for (int i = 0; guess_line != -1 && i < guess_line; ++i) {
      if (S.assigns[order[i]] == 0) { printf("NOOO %d %d\n", i, order[i]); assert(false); }
    }
#endif

    if (guess_line + 1 >= order.size()) return false;

    snapshots.push_back(guess_line);

    ++guess_line;
    const int level = S.decisionLevel();

    if (verbosity >= -3) printf("MOVING_GUESS_LINE0 %d %d\n", guess_line, level);

    // Activity based decision:
    while (guess_line != order.size()) {
      Var next = order[guess_line];
      if (toLbool(assigns[next]) == l_Undef) {
        if (guess_line != order.size() && barriers[guess_line] == -1) barriers[guess_line] = level;
        if (verbosity >= 2) {
          std::cout << "VAR_SELECT " << next << " " << guess_line << " " << level << std::endl;
        }
        check(S.assume(Lit(next, true)));
        S.undos.push_back(this);

#ifdef MY_DEBUG
        for (int i = 0; guess_line != -1 && i < guess_line; ++i) {
          if (S.assigns[order[i]] == 0) { printf("NOOO %d %d\n", i, order[i]); assert(false); }
        }
#endif

        return true;
      }
      ++guess_line;
      if (verbosity >= -3) printf("MOVING_GUESS_LINE1 %d %d %d\n", guess_line, level, guess_line == order.size() ? -1 : order[guess_line]);
    }

    if (verbosity >= 2) std::cout << "VAR_NOSELECT" << std::endl;
    S.undos.push_back(this);

#ifdef MY_DEBUG
    for (int i = 0; guess_line != -1 && i < guess_line; ++i) {
      if (S.assigns[order[i]] == 0) { printf("NOOO %d %d\n", i, order[i]); assert(false); }
    }
#endif

    return false;
}


void VarOrder::update(Var right, Solver &S) {
  if (verbosity >= -3) printf("VARORDER_UPDATE %d\n", right);

  if (pures[right]) return;
  if (isinf(tolerance)) return;
  ++update_count_since_last_stage;

  update0(right, var_ixs[right], S);
}


bool VarOrder::update0(int right, int right_ix, Solver &S) {
  if (verbosity >= -3) printf("VARORDER_UPDATE0 %d %d %d %d\n", right, right_ix, S.level[right], barriers[right_ix]);

#ifdef MY_DEBUG
    for (int i = 0; guess_line != -1 && i < guess_line; ++i) {
      if (S.assigns[order[i]] == 0) { printf("NOOO %d %d\n", i, order[i]); assert(false); }
    }
#endif

  assert(order[right_ix] == right);
  const int level = S.level[right];
  const double right_activity = activity[right];
  const double max_left_activity = right_activity - tolerance;
  const double max_left_activity_barrier = right_activity + tolerance;
  int bubble_move_count = 0;
  bool delete_barrier = true;

  int left = -1;

  int right_barrier = barriers[right_ix];
  if (right_barrier != -1) {
    if (verbosity >= -4) printf("BARRIER1 %d %d %d %d\n", right, right_barrier, level, right_ix);
    assert(right_barrier < level);
    goto after_bubbling;
  }
  
  while (right_ix) {
    int left_barrier = barriers[right_ix - 1];

    if (left_barrier == -1) {
      if (activity[left] >= max_left_activity) break;
    } else  {
      // This prevents two snapshots being at one place. Otherwise, we would need some more complex
      // mapping of places to snapshots. Now, the following mapping is ok:
      // snapshot_ix = snapshots.size() - declevel + barriers[place] + 1;
      //
      if (left_barrier < level) break;
      // We want to shift barriers as right as possible - not to backtrack too much.
      if (activity[left] > max_left_activity_barrier) break;
    }

    left = order[right_ix - 1];
    ++bubble_move_count;
    ++global_bubble_move_count;
    ++bubble_move_count_since_last_stage;
    order[right_ix] = left;
    var_ixs[left] = right_ix;

    if (left_barrier != -1) {
      if (verbosity >= -4) printf("LEFT_BARRIER %d %d %d %d\n", left_barrier, right_ix, level, S.decisionLevel());
      if (left_barrier < level) {
        if (verbosity >= -4) printf("KEEP_BARRIER\n");
        barriers[right_ix] = -1;
        --right_ix;
        delete_barrier = false;
        break;
      } else {
        assert(S.decisionLevel() - left_barrier > 0);
        int declevel = S.decisionLevel();
        if (declevel - left_barrier == 1) {
          assert(guess_line == right_ix - 1);
          if (verbosity >= -4) printf("MOVING_GUESS_LINE2 %d %d\n", guess_line, level);
          ++guess_line;
        } else {
          assert(S.decisionLevel() - left_barrier - 1 <= snapshots.size());
          unsigned snapshot_ix = snapshots.size() - declevel + left_barrier + 1;
          if (verbosity >= -4) {
            printf("MOVING_SNAPSHOT1 %d %d %d\n", snapshot_ix, snapshots[snapshot_ix], level);
          }
          assert(snapshots[snapshot_ix] == right_ix - 1);
          ++snapshots[snapshot_ix];
        }
      }
    }

    barriers[right_ix] = left_barrier;
    --right_ix;
  }
after_bubbling:

  if (bubble_move_count) {
    order[right_ix] = right;
    var_ixs[right] = right_ix;
    if (delete_barrier) barriers[right_ix] = -1;
    if (bubble_move_count > max_bubble_moves) {
      if (verbosity >= -3) {
        printf(
          "UPDATE_TOLERANCE_INCREASE %g %g %d\n",
          tolerance, tolerance * tolerance_increase, bubble_move_count
        );
      }
      tolerance *= tolerance_increase;
    }
  }

  if (verbosity >= 2) {
    std::cout
      << "UPDATE0_SUMMARY"
      << " " << right
      << " " << right_ix
      << " " << bubble_move_count
      << " " << left
      << " " << tolerance
      << " " << level
      << " " << S.decisionLevel()
      << " " << guess_line
      << std::endl;
  }

#ifdef MY_DEBUG
  for (int i = 0; guess_line != -1 && i < guess_line; ++i) {
    if (S.assigns[order[i]] == 0) { printf("NOOO %d %d\n", i, order[i]); assert(false); }
  }
#endif

  return bubble_move_count;
}
