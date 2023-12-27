#include <math.h>
#include "VarOrder.h"
#include "Solver.h"

inline void check(bool expr) { assert(expr); }

unsigned global_bubble_move_count = 0;
unsigned global_bubble_move_count_undo = 0;


void VarOrder::undo(Solver &S) {
  unsigned previous_guess_line = snapshots.back();
  snapshots.pop_back();

  if (verbosity >= 2) {
    std::cout << "VARORDER_UNDO"
      << " " << guess_line
      << " " << previous_guess_line
      << " " << order.size()
      << " " << (guess_line == order.size() ? -2 : barriers[guess_line])
      << " " << S.decisionLevel()
      << std::endl;
  }

  if (isinf(tolerance)) {
    guess_line = previous_guess_line;
    return;
  }

  unsigned bubble_move_count = 0;
  unsigned this_max_bubble_moves = max_bubble_moves;

  if (guess_line != order.size()) {
    assert(barriers[guess_line] == S.decisionLevel() - 1);
    barriers[guess_line] = -1;
  }

  if (guess_line == order.size()) --guess_line;
  while (previous_guess_line + 1 < guess_line + 1) {
    unsigned right_ix = guess_line;
    assert(barriers[right_ix] == -1 || guess_line - 1 == previous_guess_line);

    if (guess_line == 0) { --guess_line; break; }

    if (verbosity >= 2) printf("MOVING_GUESS_LINE3 %d %d\n", guess_line, previous_guess_line);
    --guess_line;

    Var left = order[guess_line];
    if (right_ix != order.size()) {
      const double min_right_activity = activity[left] + tolerance;
      Var right = order[right_ix];
      if (min_right_activity < activity[right]) {
        ++bubble_move_count;
        ++global_bubble_move_count;
        ++global_bubble_move_count_undo;
        ++bubble_move_count_since_last_stage;
        if (bubble_move_count > this_max_bubble_moves) {
          this_max_bubble_moves += max_bubble_moves;
          if (verbosity >= -3) {
            printf("UNDO_TOLERANCE_INCREASE %g %g\n", tolerance, tolerance * tolerance_increase);
          }
          tolerance *= tolerance_increase;
        }
        order[right_ix - 1] = right;
        ++right_ix;
        while (
            right_ix != order.size()
            && min_right_activity < activity[right = order[right_ix]]
        ) {
          ++bubble_move_count;
          ++global_bubble_move_count;
          ++global_bubble_move_count_undo;
          ++bubble_move_count_since_last_stage;
          if (bubble_move_count > this_max_bubble_moves) {
            this_max_bubble_moves += max_bubble_moves;
            if (verbosity >= -3) {
              printf("UNDO_TOLERANCE_INCREASE %g %g\n", tolerance, tolerance * tolerance_increase);
            }
            tolerance *= tolerance_increase;
          }
          order[right_ix - 1] = right;
          var_ixs[right] = right_ix - 1;
          ++right_ix;
        }
        order[right_ix - 1] = left;
        var_ixs[left] = right_ix - 1;
      }
    }
  }

  // if (bubble_move_count == 0) {
  //   if (verbosity >= -3) {
  //     printf("UNDO_TOLERANCE_DECREASE %g %g\n", tolerance, tolerance * tolerance_decrease);
  //   }
  //   tolerance *= tolerance_decrease;
  // }
}


Var VarOrder::select(double random_var_freq, Solver &S)
{
    if (false) {
      // Random decision:
      if (drand(random_seed) < random_var_freq){
        Var next = irand(random_seed,assigns.size());
        if (toLbool(assigns[next]) == l_Undef && !pures[next])
          return next;
      }
    }

    if (guess_line != (unsigned)-1 && guess_line >= order.size() - 1) return var_Undef;

    snapshots.push_back(guess_line);

    ++guess_line;

    const int level = S.decisionLevel();
    if (verbosity >= -3) printf("MOVING_GUESS_LINE0 %d %d\n", guess_line, level);
    unsigned move_right_count = -1;

    // Activity based decision:
    while (guess_line != order.size()) {
      Var next = order[guess_line];
      if (toLbool(assigns[next]) == l_Undef) {
        if (guess_line != order.size()) barriers[guess_line] = level;
        if (verbosity >= 2) {
          std::cout << "VAR_SELECT " << next << " " << guess_line << " " << level << std::endl;
        }
        check(S.assume(Lit(next, true)));
        S.undos.push_back(this);
        return next;
      }
      ++guess_line;
      if (verbosity >= -3) printf("MOVING_GUESS_LINE1 %d %d\n", guess_line, level);
    }

    if (verbosity >= 2) std::cout << "VAR_NOSELECT" << std::endl;
    S.undos.push_back(this);
    return var_Undef;
}


void VarOrder::update(Var right, Solver &S) {
  if (pures[right] || output_map[right] != -1) return;
  if (isinf(tolerance)) return;
  ++update_count_since_last_stage;

  int right_ix = var_ixs[right];
  const int level = S.level[right];
  const double right_activity = activity[right];
  const double max_left_activity = right_activity - tolerance;
  const double max_left_activity_barrier = right_activity + tolerance;
  unsigned bubble_move_count = 0;
  bool on_barrier = false;
  bool delete_barrier = true;

  int left = -1;
  while (right_ix) {
    left = order[right_ix - 1];
    int barrier = barriers[right_ix];
    if (barrier == -1) {
      if (activity[left] >= max_left_activity) break;
    } else {
      if (verbosity >= -4) printf("BARRIER1\n");
      if (barrier < level) {
        if (bubble_move_count == 0) on_barrier = true;
        break;
      }
      if (activity[left] >= max_left_activity) {
        if (bubble_move_count <= max_bubble_moves) on_barrier = true;
      }
      if (activity[left] > max_left_activity_barrier) break;
    }
    ++bubble_move_count;
    ++global_bubble_move_count;
    ++bubble_move_count_since_last_stage;
    order[right_ix] = left;
    var_ixs[left] = right_ix;

    int left_barrier = barriers[right_ix - 1];
    if (left_barrier != -1) {
      // TODO this is completely uncovered with our tests (yet).
      if (verbosity >= -4) printf("LEFT_BARRIER\n");
      if (left_barrier < level) {
        if (verbosity >= -4) printf("KEEP_BARRIER\n");
        --right_ix;
        delete_barrier = false;
        break;
      } else {
        assert(S.decisionLevel() - left_barrier > 0);
        if (S.decisionLevel() - left_barrier == 1) {
          assert(guess_line == right_ix - 1);
          if (verbosity >= -4) printf("MOVING_GUESS_LINE2 %d %d\n", guess_line, level);
          ++guess_line;
        } else {
          assert(S.decisionLevel() - left_barrier - 1 <= snapshots.size());
          unsigned snapshot_ix = snapshots.size() - (S.decisionLevel() - left_barrier - 1);
          if (verbosity >= -4) {
            printf("MOVING_SNAPSHOT %d %d %d\n", snapshot_ix, snapshots[snapshot_ix], level);
          }
          ++snapshots[snapshot_ix];
        }
      }
    }

    barriers[right_ix] = left_barrier;
    --right_ix;
  }

  if (bubble_move_count) {
    order[right_ix] = right;
    var_ixs[right] = right_ix;
    if (delete_barrier) barriers[right_ix] = -1;

    if (bubble_move_count > max_bubble_moves && !on_barrier) {
      if (verbosity >= -3) {
        printf(
          "UPDATE_TOLERANCE_INCREASE %g %g %d\n",
          tolerance, tolerance * tolerance_increase, bubble_move_count
        );
      }
      tolerance *= tolerance_increase;
    }
  } else {
    // if (!on_barrier) {
    //   if (verbosity >= -3) {
    //     printf("UPDATE_TOLERANCE_DECREASE %g %g\n", tolerance, tolerance * tolerance_decrease);
    //   }
    //   tolerance *= tolerance_decrease;
    // }
  }

  if (verbosity >= 2) {
    std::cout
      << "UPDATE_SUMMARY"
      << " " << right
      << " " << right_ix
      << " " << bubble_move_count
      << " " << on_barrier
      << " " << left
      << " " << tolerance
      << std::endl;
  }
}
