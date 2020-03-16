#include <iostream>


#include "Trie.h"

using std::cout;

Trie::Trie(unsigned var_count_)
: root(0, -1, NULL), var_count(var_count_), back_ptrs(var_count_), my_zeroes()
{
  my_zeroes.reserve(var_count_);
  active_hor = &root;
}


// TODO (optional) support impure_outputs
Lit Trie::guess(Solver &S) {
  if (ver_ix >= 0) {
    return S.outputs[active_hor->vers[hor_ix].hors[ver_ix].tag];
  }
  if (hor_ix < active_hor->vers.size()) {
    return S.outputs[active_hor->vers[hor_ix].tag];
  }
  else {
    active_var_old = active_var;

    while (active_var < var_count) {
      if (S.value(S.outputs[active_var]) == l_Undef) {
        S.undos[var(S.outputs[active_var])].push(this);
        back_ptrs[active_var] = active_var_old;
        active_var_old = var_count; // ~ NULL
        printf("guess %d %d\n", active_var, var(S.outputs[active_var]));
        return S.outputs[active_var++];
      }
      active_var++;
    }
    printf("noguess\n");
    return lit_Undef;
  }
}


void Trie::onSat(Solver &S) {
  // unordered_set<unsigned> my_zeroes_set(my_zeroes.begin(), my_zeroes.end());

  // VerStart &ver = active_hor->vers.emplace_back();
  // ver.hors.reserve(var_count - my_zeroes.size());

  // unsigned x = 0;
  // for (;; x++) {
  //   if (S.value(S.outputs[x]) == l_False) break;
  // }
  // ver.tag = x;

  // unsigned parent_hor_ix = active_hor->vers.size();
  // unsigned i = 0;
  // for (x++; x < var_count; x++) {
  //   ver.hors.emplace_back(x, parent_hor_ix, i, active_hor);
  //   i++;
  // }

  // cout << active_hor->vers.size() << "add\n";

  // bool keep_watch;
  // propagate(S, Lit(), keep_watch);
}


void Trie::remove(Solver& S, bool just_dealloc) {
  std::cerr << "SubsetQ removed!\n";
}

bool Trie::simplify(Solver& S) {
  return false;
}


WhatToDo Trie::after_hors_change(Solver &S) {
  if (hor_ix == active_hor->vers.size()) {
    return WhatToDo::DONE;
  }

  int out = active_hor->vers[hor_ix].tag;
  lbool val = S.value(S.outputs[out]);

  if (val == l_Undef) {
    if (active_hor->vers[hor_ix].hors.size() == 0) return WhatToDo::PROPAGATE;
    return WhatToDo::WATCH;
  }
  if (val == l_False) return WhatToDo::CONFLICT;
  return WhatToDo::AGAIN;
}


WhatToDo Trie::after_vers_change(Solver &S) {
  int out = active_hor->vers[hor_ix].hors[ver_ix].tag;
  lbool val = S.value(S.outputs[out]);

  if (val == l_Undef) {
    if (ver_ix == int(active_hor->vers[hor_ix].hors.size()) - 1) {
      return WhatToDo::PROPAGATE;
    }
    return WhatToDo::WATCH;
  }
  if (val == l_False) return WhatToDo::CONFLICT;
  return WhatToDo::AGAIN;
}


bool Trie::propagate(Solver& S, Lit _p, bool& keep_watch) {
  WhatToDo what_to_do;

  while (true) {
    if (ver_ix >= 0) {
      int out = active_hor->vers[hor_ix].hors[ver_ix].tag;
      S.undos[var(S.outputs[out])].push(this);

      if (S.value(S.outputs[out]) == l_True) {
        active_hor = &active_hor->vers[hor_ix].hors[ver_ix].hor;
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
      int out = active_hor->vers[hor_ix].tag;
      S.undos[var(S.outputs[out])].push(this);

      if (S.value(S.outputs[out]) == l_True) {
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
      case AGAIN: continue;
      case WATCH:
        if (ver_ix >= 0) {
          int out = active_hor->vers[hor_ix].hors[ver_ix].tag;
          S.watches[index(S.outputs[out])].push(this);
          S.watches[index(~S.outputs[out])].push(this);
        }
        else {
          int out = active_hor->vers[hor_ix].tag;
          S.watches[index(S.outputs[out])].push(this);
          S.watches[index(~S.outputs[out])].push(this);
        }
        return true;
      case DONE: return true;
      case PROPAGATE: {
        int out = ver_ix >= 0
              ? active_hor->vers[hor_ix].hors[ver_ix].tag
              : active_hor->vers[hor_ix].tag;
        return S.enqueue(S.outputs[out], this);
      }
      case CONFLICT: return false;
    }
  }
}


void Trie::undo(Solver& S, Lit p) {
  if (undo_skip_count) {
    undo_skip_count--;
    return;
  }

  if (active_var > 0) {
    if (active_var_old != var_count) {
      active_var = active_var_old;
      active_var_old = var_count;
    }
    printf("undo %d %d %d\n", active_var - 1, S.output_map[var(p)], var(S.outputs[active_var - 1]));
    active_var = back_ptrs[active_var - 1];
  }
  else back();
}


void Trie::back() {
  if (ver_ix >= 0) {
    ver_ix--;
    my_zeroes.pop_back();
  }
  else if (hor_ix > 0) hor_ix--;
  else {
    hor_ix = active_hor->parent_hor_ix;
    ver_ix = active_hor->parent_ver_ix;
    active_hor = active_hor->parent;
  }
}


void Trie::calcReason(Solver& S, Lit p, vec<Lit>& out_reason) {
  if (p != lit_Undef) {
    unsigned culprit = S.output_map[var(p)];
    unsigned out;
    do {
      back();
      undo_skip_count++;
      out = ver_ix >= 0
        ? active_hor->vers[hor_ix].hors[ver_ix].tag
        : active_hor->vers[hor_ix].tag;
    } while (out != culprit);
  }

  for (unsigned x: my_zeroes) {
    out_reason.push(~S.outputs[x]);
  }
}
