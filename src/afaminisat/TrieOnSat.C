#ifdef AFA

#include <algorithm>

#include "Trie.h"
#include "Solver.h"

using std::cout;
using std::endl;

void Trie::onSat(
  Solver &S,
  unsigned clause_count,
  vector<unsigned> &sharing_set,
  vec<Lit> &zero_outputs,
  vector<AfaHorline> &horlines,
  vector<Head*> &verlines
) {
  Head * deepest_place = deepest_rightmost_rear;
  if (verbosity >= 2) {
    std::cout << "ON_SAT0"
      << " " << deepest_place
      << " " << S.root_level
      << std::endl;
  }
  if (verbosity >= 2) {
    std::cout << "ON_SAT"
      << " " << HeadAttrs(deepest_place, S)
      << " " << S.root_level
      << std::endl;
  }

  int last_rear_level = 0;
  Head *last_rear = NULL; 

#ifndef ALL_SOLO
  int last_van_level = 0;
  int minus_first_rear_level = 0;
#endif

  {
    Head *iter = deepest_place;
    while (true) {
      if (iter->is_ver) iter = iter->above;
      else iter = iter->above == NULL ? NULL : iter->above->above;

      if (iter == NULL) break;

      if (verbosity >= 2) {
        cout << "MY_ZERO1"
          << " " << iter->tag
          << " " << S.value(iter->tag).toInt()
          << " " << S.level[var(iter->tag)]
          << endl;
      }

      const Lit tag = iter->tag;
      sharing_set[index(tag)] = clause_count;

      int lvl = S.level[var(tag)];
      if (lvl >= last_rear_level) {
#ifndef ALL_SOLO
        minus_first_rear_level = -1;
        last_van_level = last_rear_level;
#endif
        last_rear_level = lvl;
        last_rear = iter;
      }
#ifndef ALL_SOLO
      else if (lvl >= minus_first_rear_level) {
        minus_first_rear_level = lvl;
      }
#endif
    }
  }

  // max level of added_vars+my_zeroes
  int max_level = -1;

  // added_vars are (level, variable) pairs, of zero variables added in the
  // accepting condition (= not included in my_zeroes)
  vector<std::pair<int, Lit>> added_vars;
  added_vars.reserve(zero_outputs.size());

  {
    const Lit* end = &zero_outputs[zero_outputs.size()];
    for (Lit *xptr = zero_outputs; xptr != end; ++xptr) {
      Lit x = *xptr;
      if (verbosity >= 2) {
        printf("MY_ZERO2 " L_LIT " %d %d\n", L_lit(x), S.value(x).toInt(), S.level[var(x)]);
      }
      int lvl = S.level[var(x)];
      if (lvl > max_level) {
        max_level = lvl;
      }
      if (sharing_set[index(x)] != clause_count) {
        added_vars.emplace_back(lvl, x);
      }
    }
  }

  if (verbosity >= 2) printf("MAX_LEVEL %d\n", max_level);

  bool ver_accept = deepest_place->is_ver;

  // We have found a solution that covers the last traversed clause => we
  // shrink the clause (cut it up to the knee) instead of adding a new branch
  // to the trie.
  if (added_vars.size() == 0) {
    Head *cut;
    assert(deepest_place->above != NULL);
    if (ver_accept) cut = deepest_place->above;
    else cut = deepest_place->above->above;

    if (verbosity >= 2) cout << "NO_ADDED_VAR " << *cut << endl;
    cut->down = NULL;
    S.cancelUntil(max_level);
    return;
  }

  // sort added_vars by level
  std::sort(added_vars.begin(), added_vars.end());

  if (verbosity >= 2) {
    for (auto x: added_vars) {
       printf("ADDED_VAR %d " L_LIT "\n", x.first, L_lit(x.second));
    }
  }

  // Add the branch with unshared part of the clause (added_vars)

  Head *verheadptr;

  {
    int horline_ix;

    if (deepest_place->is_ver) {
      horline_ix = horlines.size();
      AfaHorline &horline = horlines.emplace_back(deepest_place);
      verheadptr = &horline.elems.emplace_back(added_vars[0].second);
      verheadptr->above = deepest_place;
    } else {
      horline_ix = deepest_place->external;
      AfaHorline &horline = horlines[horline_ix];
      verheadptr = &horline.elems.emplace_back(added_vars[0].second);
      verheadptr->above = horline.leftmost;
    }
    Head &verhead = *verheadptr;

    verhead.right = NULL;
    verhead.external = horline_ix;
    unsigned depth = verhead.depth = deepest_place->depth;
    deepest_place->right = verheadptr;

    Head *verline = verlines.emplace_back(new Head[added_vars.size() - 1]);

    Head *above = verheadptr;
    for (unsigned i = 1; i != added_vars.size(); ++i) {
      Head &horhead = verline[i - 1];
      horhead.tag = added_vars[i].second;
      horhead.above = above;

      if (i == 1) verhead.down = &horhead;
      else above->down = &horhead;

      horhead.depth = ++depth;
      above = &horhead;
    }

    deepest_rightmost_rear = above;
  }

  // Calculate Plus and Minus snapshots in the new branch.
  if (verbosity >= 2) {
    cout << "ON_SAT_SNAPS"
      << " R0=" << last_rear_level
#ifndef ALL_SOLO
      << " V0=" << last_van_level
      << " VM=" << minus_first_rear_level
#endif
      << " R=" << *last_rear
      << endl;
  }

#ifndef ALL_SOLO
  last_van_level = max(minus_first_rear_level, last_van_level);
#endif

  Head *van_place = verheadptr;

  {

#ifndef ALL_SOLO
    while (last_van_level < last_rear_level) {
      int lvl;
      while ((lvl = S.level[var(van_place->tag)]) <= last_van_level) {
        van_place = van_place->down;
        if (van_place == NULL) goto no_van_place;
      }
      lvl = min(lvl, last_rear_level);
      if (lvl > S.root_level) {
        LogList<MinusSnapshot> &msnaps = last_van_level > S.root_level
          ? snapshots[last_van_level - S.root_level - 1].minus_snapshots
          : root_minus_snapshots;
        MinusSnapshot &last_van_msnap = msnaps.emplace_back(van_place);
        snapshots[lvl - S.root_level - 1].plus_snapshots.emplace_back(
          van_place, last_van_level, last_rear, &last_van_msnap, (Head*)NULL
        );

        if (verbosity >= 2) {
          cout << "VAN1"
            << " " << van_place
            << " -" << last_van_level
            << " +" << lvl
            << " ^" << last_rear
            << endl;
        }
      } else if (verbosity >= 2) {
        cout << "VAN1_SKIP " << van_place << " " << lvl << " " << S.root_level << endl;
      }
      last_van_level = lvl;
    }
#endif

    Head *rear_place = van_place;
    van_place = van_place->down;

    if (van_place == NULL) goto no_van_place;

    while(true) {
      int lvl;
      while ((lvl = S.level[var(rear_place->tag)]) <= last_rear_level) {
        rear_place = van_place;
        van_place = van_place->down;
        if (van_place == NULL) goto no_van_place;
      }

      Snapshot &snapshot = snapshots[lvl - S.root_level - 1];

#ifndef ALL_SOLO
      if (lvl > S.root_level) {
        LogList<MinusSnapshot> &msnaps = last_van_level > S.root_level
          ? snapshots[last_van_level - S.root_level - 1].minus_snapshots
          : root_minus_snapshots;
        MinusSnapshot &last_van_msnap = msnaps.emplace_back(van_place);
        snapshot.plus_snapshots.emplace_back(
          van_place, last_van_level, rear_place, &last_van_msnap, (Head*)NULL
        );
        if (verbosity >= 2) {

          cout << "VAN2"
            << " " << van_place
            << " -" << last_van_level
            << " +" << lvl
            << " ^" << rear_place
            << endl;
        }
      } else if (verbosity >= 2) {
        cout << "VAN2_SKIP " << van_place << " " << lvl << " " << S.root_level << endl;
      }
      last_van_level = lvl;
#endif

#ifdef ALL_SOLO
      rear_place->guard.guard_type = SOLO_GUARD;
#else
      rear_place->guard.guard_type = REAR_GUARD;
      rear_place->guard.dual = NULL;
      rear_place->guard.deepest_rightmost_van = NULL;
#endif

      if (lvl > S.root_level) {
        LogList<MinusSnapshot> &msnaps = last_rear_level > S.root_level
          ? snapshots[last_rear_level - S.root_level - 1].minus_snapshots
          : root_minus_snapshots;
        MinusSnapshot &last_rear_msnap = msnaps.emplace_back(rear_place);
        snapshot.rear_plus_snapshots.emplace_back(
          rear_place, last_rear_level, (Head*)NULL, &last_rear_msnap, rear_place
        );

        if (verbosity >= 2) {
          cout << "REAR2"
            << " " << rear_place
            << " -" << last_rear_level
            << " +" << lvl
            << endl;
        }
      } else if (verbosity >= 2) {
        cout << "REAR2_SKIP " << rear_place << " " << lvl << " " << S.root_level << endl;
      }
      last_rear_level = lvl;
    }
  }

no_van_place:;

  S.cancelUntil(max_level);
}

#endif
