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
      << " " << (guess_line == order.size() ? -2 : barriers[guess_line].first)
      << "," << (guess_line == order.size() ? -2 : barriers[guess_line].second)
      << " " << (
        snapshots.back() == order.size()
        ? -2 : (snapshots.back() == -1 ? -3 : barriers[snapshots.back()].first)
      )
      << "," << (
        snapshots.back() == order.size()
        ? -2 : (snapshots.back() == -1 ? -3 : barriers[snapshots.back()].second)
      )
      << " " << S.decisionLevel()
      << std::endl;
  }

#ifdef MY_DEBUG
  for (int i = 0; snapshots.back() != -1 && i < snapshots.back(); ++i) {
    if (assigns[order[i]] == 0) { printf("NOOO %d %d\n", i, order[i]); assert(false); }
  }
#endif

  if (isinf(tolerance)) {
    guess_line = snapshots.back();
    return;
  }

  unsigned bubble_move_count = 0;
  unsigned this_max_bubble_moves = max_bubble_moves;

  int right_ix = guess_line;

  if (guess_line != order.size()) {
    pair<int, int> barrier = barriers[guess_line];
    assert(barrier.second == S.decisionLevel() - 1);
    if (barrier.first < barrier.second) {
      --barriers[guess_line].second;
      snapshots.back() = guess_line;
    } else {
      barriers[guess_line] = pair(-1, -1);
      guess_line = snapshots.back();
    }
  } else guess_line = snapshots.back();

  snapshots.pop_back();

  assert(
    guess_line == 0 || guess_line == order.size() ||
    barriers[guess_line].second == S.decisionLevel() - 2
  );

  for (; right_ix != order.size(); ++right_ix) {
    if (update0(order[right_ix], right_ix, S, S.decisionLevel() - 1) == 0) break;
  }

#ifdef MY_DEBUG
  for (int i = 0; i < guess_line; ++i) {
    if (assigns[order[i]] == 0) { printf("NOOO %d %d\n", i, order[i]); assert(false); }
  }
#endif
}


bool VarOrder::select(Solver &S)
{
    if (verbosity >= -3) printf("VARORDER_SELECT %d\n", guess_line);

#ifdef MY_DEBUG
    for (int i = 0; i < guess_line; ++i) {
      if (assigns[order[i]] == 0) { printf("NOOO %d %d\n", i, order[i]); assert(false); }
    }
#endif

    if (guess_line >= order.size()) return false;

    snapshots.push_back(guess_line);

    const int level = S.decisionLevel();

    if (verbosity >= -3) printf("MOVING_GUESS_LINE0 %d %d\n", guess_line, level);

    // Activity based decision:
    while (guess_line != order.size()) {
      Var next = order[guess_line];
      if (toLbool(assigns[next]) == l_Undef) {
        if (guess_line != order.size()) {
          pair<int, int> &barrier = barriers[guess_line];
          barrier.second = level;
          if (barrier.first == -1) barrier.first = level;
        }
        if (verbosity >= 2) {
          std::cout << "VAR_SELECT " << next << " " << guess_line << " " << level << std::endl;
        }
        check(S.assume(Lit(next, true)));
        S.undos.push_back(this);

#ifdef MY_DEBUG
        for (int i = 0; i < guess_line; ++i) {
          if (assigns[order[i]] == 0) { printf("NOOO %d %d\n", i, order[i]); assert(false); }
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
    for (int i = 0; i < guess_line; ++i) {
      if (assigns[order[i]] == 0) { printf("NOOO %d %d\n", i, order[i]); assert(false); }
    }
#endif

    return false;
}


void VarOrder::update(Var right, Solver &S) {
  if (verbosity >= -3) printf("VARORDER_UPDATE %d\n", right);

  if (pures[right]) return;
  if (isinf(tolerance)) return;
  ++update_count_since_last_stage;

  update0(right, var_ixs[right], S, S.decisionLevel());
}


bool VarOrder::update0(int right, int right_ix, Solver &S, int declevel) {
  const int level = S.level[right];

  if (verbosity >= -3) printf(
    "VARORDER_UPDATE0 %d %d %d %d,%d\n",
    right, right_ix, level, barriers[right_ix].first, barriers[right_ix].second
  );

#ifdef MY_DEBUG
    for (int i = 0; i < guess_line; ++i) {
      if (assigns[order[i]] == 0) { printf("NOOO %d %d\n", i, order[i]); assert(false); }
    }
#endif

  assert(order[right_ix] == right);
  const double right_activity = activity[right];
  const double max_left_activity = right_activity - tolerance;
  const double max_left_activity_barrier = right_activity + tolerance;
  int bubble_move_count = 0;

  int left = -1;

  pair<int, int> right_barrier = barriers[right_ix];
  if (right_barrier.second != -1) {
    if (verbosity >= -4) printf(
      "BARRIER1 %d %d,%d %d %d\n",
      right,
      right_barrier.first,
      right_barrier.second,
      level,
      right_ix
    );
    assert(right_barrier.second < level);
    goto after_bubbling;
  }
  
  while (right_ix) {
    pair<int, int> left_barrier = barriers[right_ix - 1];
    assert(left_barrier.first <= left_barrier.second);
    assert((left_barrier.second == -1) == (left_barrier.first == -1));

    left = order[right_ix - 1];

    if (left_barrier.second == -1) {
      if (activity[left] >= max_left_activity) break;
    } else  {
      // We want to shift barriers as right as possible - not to backtrack too much.
      if (activity[left] > max_left_activity_barrier) break;
    }

    ++bubble_move_count;
    ++global_bubble_move_count;
    ++bubble_move_count_since_last_stage;
    order[right_ix] = left;
    var_ixs[left] = right_ix;

    if (left_barrier.second != -1) {
      if (verbosity >= -4) printf(
        "LEFT_BARRIER %d,%d %d %d %d\n",
        left_barrier.first,
        left_barrier.second,
        right_ix,
        level,
        declevel
      );

      if (left_barrier.second < level) {
        if (verbosity >= -4) printf("KEEP_BARRIER\n");
        barriers[right_ix] = pair(-1, -1);
        --right_ix;
        break;
      }

      if (left_barrier.first < level) {
        if (verbosity >= -4) printf("SPLIT_BARRIER\n");
        barriers[right_ix - 1] = pair(left_barrier.first, level - 1);
        unsigned snapshot_ix = snapshots.size() - declevel + level;
        snapshots[snapshot_ix] = right_ix - 1;

        unsigned new_barrier_first = level;

        for (unsigned i = right_ix; i < order.size(); ++i) {
          int ivar = order[i];
          int ilevel = assigns[ivar] == 0 ? std::numeric_limits<int>::max() : S.level[ivar];
          if (verbosity >= 2) {
            std::cout << "VARORDER_IVAR"
              << " " << i
              << " " << ivar
              << " " << ilevel
              << " " << barriers[i].first
              << "," << barriers[i].second
              << std::endl;
          }
          assert (
            barriers[i].first == -1
            || barriers[i].first == left_barrier.second + 1
               && barriers[i].first < ilevel
          );

          if (new_barrier_first < ilevel) {
            if (left_barrier.second < ilevel) {
              if (barriers[i].second == -1) {
                barriers[i] = pair(new_barrier_first, left_barrier.second);

                if (declevel - left_barrier.second == 1) {
                  if (verbosity >= -4) printf("SET_GUESS_LINE %d %d %d\n", guess_line, level, i);
                  guess_line = i;
                } else {
                  unsigned snapshot_ix = snapshots.size() - declevel + left_barrier.second + 1;
                  if (verbosity >= -4) {
                    printf("SET_SNAPSHOT1 %d %d %d %d\n", snapshot_ix, snapshots[snapshot_ix], level, i);
                  }
                  snapshots[snapshot_ix] = i;
                }
              } else barriers[i].first = new_barrier_first;
              break;
            } else {
              barriers[i] = pair(new_barrier_first, ilevel - 1);
              unsigned snapshot_ix = snapshots.size() - declevel + ilevel;
              if (verbosity >= -4) {
                printf("SET_SNAPSHOT2 %d %d %d %d\n", snapshot_ix, snapshots[snapshot_ix], level, i);
              }
              snapshots[snapshot_ix] = i;
              new_barrier_first = ilevel;
            }
          };
        }

        --right_ix;
        break;
      }

      assert(declevel - left_barrier.second > 0);
      if (declevel - left_barrier.second == 1) {
        assert(guess_line == right_ix - 1);
        if (verbosity >= -4) printf("MOVING_GUESS_LINE2 %d %d\n", guess_line, level);
        ++guess_line;
      } else {
        assert(declevel - left_barrier.second - 1 <= snapshots.size());
        unsigned snapshot_ix = snapshots.size() - declevel + left_barrier.second + 1;
        if (verbosity >= -4) {
          printf("MOVING_SNAPSHOT1 %d %d %d\n", snapshot_ix, snapshots[snapshot_ix], level);
          std::cout << std::flush;
        }
        assert(snapshots[snapshot_ix] == right_ix - 1);
        ++snapshots[snapshot_ix];
      }

    }

    barriers[right_ix - 1] = pair(-1, -1);
    barriers[right_ix] = left_barrier;
    --right_ix;
  }
after_bubbling:

  if (bubble_move_count) {
    order[right_ix] = right;
    var_ixs[right] = right_ix;
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
  for (int i = 0; i < guess_line; ++i) {
    if (assigns[order[i]] == 0) { printf("NOOO %d %d\n", i, order[i]); assert(false); }
  }
#endif

  return bubble_move_count;
}
