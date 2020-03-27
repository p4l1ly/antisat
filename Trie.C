#include <algorithm>
#include <iostream>
#include <tuple>
#include <boost/iterator/transform_iterator.hpp>


#include "Trie.h"

using std::cout;

void BackJumper::undo(Solver &S, Lit _p) {
  S.trie->active_hor = active_hor;
  S.trie->hor_ix = hor_ix;
  S.trie->ver_ix = ver_ix;
  S.trie->my_zeroes.erase(
      S.trie->my_zeroes.begin() + my_zeroes_size,
      S.trie->my_zeroes.end()
  );

  printf("UNDO %d %d %d %lu\n", active_hor->topo, hor_ix, ver_ix, active_hor->vers->size());
  Lit out_lit = S.outputs[ver_ix >= 0
    ? (*(*active_hor->vers)[hor_ix].hors)[ver_ix].tag
    : (*active_hor->vers)[hor_ix].tag
  ];
  S.watches[index(out_lit)].push(S.trie);
  S.watches[index(~out_lit)].push(S.trie);
  printf("WU %d\n", var(out_lit));
}

Trie::Trie(unsigned var_count_)
: root(0, NULL),
  var_count(var_count_),
  back_ptrs(var_count_),
  my_zeroes(),
  propagations()
{
  my_zeroes.reserve(var_count_);
  active_hor = &root;
}


// TODO (optional) support impure_outputs
Lit Trie::guess(Solver &S) {
  if (ver_ix != -1) {
    HorHead &hor_head = (*(*active_hor->vers)[hor_ix].hors)[ver_ix];
    Lit out_lit = S.outputs[hor_head.tag];

    hor_head.backjumper->my_zeroes_size = my_zeroes.size();
    S.undos[var(out_lit)].push(hor_head.backjumper);
    printf("GUESS_VER %d %d %d %d %d\n", active_hor->topo, hor_ix, ver_ix, hor_head.tag, var(out_lit));
    return out_lit;
  }
  if (hor_ix < active_hor->vers->size()) {
    VerHead &ver_head = (*active_hor->vers)[hor_ix];
    Lit out_lit = S.outputs[ver_head.tag];

    ver_head.backjumper->my_zeroes_size = my_zeroes.size();
    S.undos[var(out_lit)].push(ver_head.backjumper);
    printf("GUESS_HOR %d %d %d %d %d\n", active_hor->topo, hor_ix, ver_ix, ver_head.tag, var(out_lit));
    return out_lit;
  }
  else {
    if (active_var == var_count) return lit_Undef;
    active_var_old = active_var;

    while (active_var < var_count) {
      Lit p = S.outputs[active_var];
      if (S.value(p) == l_Undef) {
        printf("GUESS_ACC %d %d\n", active_var, var(p));
        S.undos[var(p)].push(this);
        back_ptrs[active_var] = active_var_old;
        active_var_old = var_count; // ~ NULL
        active_var++;
        return p;
      }
      active_var++;
    }
    // printf("noguess %d\n", active_var_old);
    return lit_Undef;
  }
}

inline unsigned tuple_snd(const std::tuple<int, unsigned> &x) {
  return std::get<1>(x);
}

BackJumper* Trie::onSat(Solver &S) {
  printf("ON_SAT\n");
  S.stats.conflicts++;

  unordered_set<unsigned> my_zeroes_set(my_zeroes.begin(), my_zeroes.end());

  int max_level = -1;
  vector<std::tuple<int, unsigned>> added_vars;
  for (unsigned x = 0; x < var_count; x++) {
    if (S.value(S.outputs[x]) == l_False) {
      max_level = max(max_level, S.level[var(S.outputs[x])]);
      if (!my_zeroes_set.contains(x)) {
        added_vars.emplace_back(S.level[var(S.outputs[x])], x);
      }
    }
  }

  std::sort(added_vars.begin(), added_vars.end());

  for (auto x: added_vars) {
    printf("ADDED_VAR %d %d %d\n", std::get<0>(x), std::get<1>(x), var(S.outputs[std::get<1>(x)]));
  }

  printf("MAX_LEVEL %d\n", max_level);

  if (added_vars.size() == 0) {
    printf("NO_ADDED_VAR\n");
    S.cancelUntil(max_level);
    return active_hor->back;
  }

  const std::tuple<int, unsigned>& x = added_vars[0];
  VerHead &ver = active_hor->vers->emplace_back(
    std::get<1>(x), active_hor, hor_ix, -1);

  ver.hors->reserve(var_count - my_zeroes.size());

  unsigned my_zeroes_size = my_zeroes.size();

  if (std::get<0>(x) > last_state_level) {
    last_state_level = std::get<0>(x);
    ver.backjumper->my_zeroes_size = my_zeroes_size;
    S.undos[var(S.outputs[std::get<1>(x)])].push(ver.backjumper);
  }

  unsigned parent_hor_ix = active_hor->vers->size() - 1;
  for (unsigned i = 1; i < added_vars.size(); i++) {
    const std::tuple<int, unsigned>& x = added_vars[i];
    HorHead &hor_head = ver.hors->emplace_back(
        std::get<1>(x), active_hor, parent_hor_ix, i - 1);

    if (std::get<0>(x) > last_state_level) {
      last_state_level = std::get<0>(x);
      hor_head.backjumper->my_zeroes_size = my_zeroes_size + i;
      S.undos[var(S.outputs[std::get<1>(x)])].push(hor_head.backjumper);
    }
  }

  max_level = max(max_level, std::get<0>(added_vars.back()));

  auto beg = boost::make_transform_iterator(added_vars.begin(), tuple_snd);
  auto end = boost::make_transform_iterator(added_vars.end(), tuple_snd);
  my_zeroes.reserve(my_zeroes.size() + added_vars.size());
  my_zeroes.insert(my_zeroes.end(), beg, end);

  S.cancelUntil(max_level);
  return NULL;
}

void BackJumper::cut() {
  vector<HorHead> &hors = *(*active_hor->vers)[hor_ix].hors;
  hors.erase(hors.begin() + ver_ix, hors.end());
}


void Trie::remove(Solver& S, bool just_dealloc) {
  std::cerr << "SubsetQ removed!\n";
}

bool Trie::simplify(Solver& S) {
  return false;
}


WhatToDo Trie::after_hors_change(Solver &S) {
  if (hor_ix == active_hor->vers->size()) {
    return WhatToDo::DONE;
  }

  VerHead &ver_head = (*active_hor->vers)[hor_ix];
  int out = ver_head.tag;
  lbool val = S.value(S.outputs[out]);

  if (val == l_Undef) {
    if (ver_head.hors->size() == 0) return WhatToDo::PROPAGATE;
    return WhatToDo::WATCH;
  }
  if (val == l_False && ver_head.hors->size() == 0) {
    my_zeroes.push_back(out);
    return WhatToDo::CONFLICT;
  }
  return WhatToDo::AGAIN;
}


WhatToDo Trie::after_vers_change(Solver &S) {
  VerHead &ver_head = (*active_hor->vers)[hor_ix];
  int out = (*ver_head.hors)[ver_ix].tag;
  printf("OUT %d\n", out);
  lbool val = S.value(S.outputs[out]);

  if (val == l_Undef) {
    if (ver_ix == int(ver_head.hors->size()) - 1) {
      return WhatToDo::PROPAGATE;
    }
    return WhatToDo::WATCH;
  }
  if (val == l_False && ver_ix == int(ver_head.hors->size()) - 1) {
    my_zeroes.push_back(out);
    return WhatToDo::CONFLICT;
  }
  return WhatToDo::AGAIN;
}


bool Trie::propagate(Solver& S, Lit p, bool& keep_watch) {
  printf("PROP %d %d %d %d\n", active_hor->topo, hor_ix, ver_ix, var(p));

  if (hor_ix >= active_hor->vers->size()) return true;

  unsigned out = ver_ix >= 0
    ? (*(*active_hor->vers)[hor_ix].hors)[ver_ix].tag
    : (*active_hor->vers)[hor_ix].tag;
  Lit out_lit = S.outputs[out];

  if (var(out_lit) != var(p)) return true;

  WhatToDo what_to_do;

  while (true) {
    if (ver_ix != -1) {
      if (S.value(out_lit) == l_True) {
        HorHead &hor_head = (*(*active_hor->vers)[hor_ix].hors)[ver_ix];
        active_hor = hor_head.hor;
        hor_ix = 0;
        ver_ix = -1;
        what_to_do = after_hors_change(S);
      }
      else {
        my_zeroes.push_back(out);
        ver_ix++;
        what_to_do = after_vers_change(S);
      }
    }
    else {
      if (S.value(out_lit) == l_True) {
        hor_ix++;
        what_to_do = after_hors_change(S);
      }
      else {
        my_zeroes.push_back(out);
        ver_ix++;
        what_to_do = after_vers_change(S);
      }
    }

    switch (what_to_do) {
      case AGAIN: {
        printf("AGAIN %d %d %d\n", active_hor->topo, hor_ix, ver_ix);
        out = ver_ix >= 0
          ? (*(*active_hor->vers)[hor_ix].hors)[ver_ix].tag
          : (*active_hor->vers)[hor_ix].tag;
        out_lit = S.outputs[out];
        continue;
      }

      case WATCH: {
        printf("WATCH %d %d %d\n", active_hor->topo, hor_ix, ver_ix);
        out_lit = S.outputs[ver_ix != -1
          ? (*(*active_hor->vers)[hor_ix].hors)[ver_ix].tag
          : (*active_hor->vers)[hor_ix].tag
        ];
        S.watches[index(out_lit)].push(this);
        S.watches[index(~out_lit)].push(this);
        printf("WW %d\n", var(out_lit));
        return true;
      }

      case DONE: {
        printf("DONE %d %d %d\n", active_hor->topo, hor_ix, ver_ix);
        last_state_level = S.decisionLevel();
        return true;
      }

      case PROPAGATE: {
        printf("PROPAGATE %d %d %d\n", active_hor->topo, hor_ix, ver_ix);
        BackJumper *backjumper;

        if (ver_ix != -1) {
            HorHead &hor_head = (*(*active_hor->vers)[hor_ix].hors)[ver_ix];
            out_lit = S.outputs[hor_head.tag];
            backjumper = hor_head.backjumper;
        }
        else {
            VerHead &ver_head = (*active_hor->vers)[hor_ix];
            out_lit = S.outputs[ver_head.tag];
            backjumper = ver_head.backjumper;
        }

        S.watches[index(out_lit)].push(this);
        S.watches[index(~out_lit)].push(this);
        printf("WP %d\n", var(out_lit));

        backjumper->my_zeroes_size = my_zeroes.size();
        propagations.push_back(backjumper);
        return S.enqueue(out_lit, this);
      }

      case CONFLICT: {
          printf("CONFLICT %d %d %d\n", active_hor->topo, hor_ix, ver_ix);
          return false;
      }
    }
  }
}


void Trie::undo(Solver& S, Lit p) {
  if (active_var_old != var_count) {
    active_var = active_var_old;
    active_var_old = var_count;
  }

  active_var = back_ptrs[active_var - 1];
}


void Trie::calcReason(Solver& S, Lit p, vec<Lit>& out_reason) {
  if (p == lit_Undef) {
    int max_level = -1;
    for (unsigned x: my_zeroes) {
      Lit out_lit = S.outputs[x];
      max_level = max(max_level, S.level[var(out_lit)]);
      out_reason.push(~out_lit);
    }
    S.cancelUntil(max_level);
  }
  else {
    propagations.back()->undo(S, lit_Undef);
    propagations.pop_back();

    for (unsigned x: my_zeroes) {
      out_reason.push(~S.outputs[x]);
    }
  }

  printf("CALC_REASON %d", var(p)); for (unsigned x: my_zeroes) { printf(" %u", x); } printf("\n");
}


void Trie::reset(Solver &S) {
  active_hor = &root;
  hor_ix = 0;
  ver_ix = -1;
  active_var = 0;
  active_var_old = 0;
  propagations.clear();
  my_zeroes.clear();

  printf("RESET\n");

  if (root.vers->size()) {
    Lit out_lit = S.outputs[(*root.vers)[0].tag];
    S.watches[index(out_lit)].push(this);
    S.watches[index(~out_lit)].push(this);
    printf("WR %d\n", var(out_lit));
  }
}
