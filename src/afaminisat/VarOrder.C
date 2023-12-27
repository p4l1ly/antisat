#include <math.h>
#include "VarOrder.h"
#include "Solver.h"


unsigned global_bubble_move_count = 0;
unsigned global_bubble_move_count_undo = 0;


void VarOrder::undo(Solver &S) {
  unsigned previous_guess_line = snapshots.back();
  snapshots.pop_back();

  if (isinf(tolerance)) {
    guess_line = previous_guess_line;
    return;
  }

  unsigned bubble_move_count = 0;
  unsigned this_max_bubble_moves = max_bubble_moves;

  if (guess_line != order.size()) {
    assert(barriers[guess_line] == S.decisionLevel());
    barriers[guess_line] = -1;
  }

  while (previous_guess_line < guess_line) {
    unsigned right_ix = guess_line--;
    assert(barriers[guess_line] == -1 || guess_line == previous_guess_line);

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

    snapshots.push_back(guess_line);
    S.undos.push_back(this);

    const int level = S.decisionLevel();
    unsigned move_right_count = -1;

    // Activity based decision:
    while (guess_line != order.size()) {
      Var next = order[guess_line++];
      if (toLbool(assigns[next]) == l_Undef) {
        if (guess_line != order.size()) barriers[guess_line] = level;
        if (verbosity >= 2) {
          std::cout << "SELECT " << next << " " << guess_line << " " << level << std::endl;
        }
        return next;
      }
    }

    if (verbosity >= 2) std::cout << "NOSELECT" << std::endl;
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

  while (right_ix) {
    int left = order[right_ix - 1];
    int barrier = barriers[right_ix];
    if (barrier == -1) {
      if (activity[left] >= max_left_activity) break;
    } else {
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
    barriers[right_ix] = barriers[right_ix - 1];
    --right_ix;
  }

  if (bubble_move_count) {
    order[right_ix] = right;
    var_ixs[right] = right_ix;
    barriers[right_ix] = -1;

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
      << std::endl;
  }
}
