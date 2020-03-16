#ifndef Trie_h
#define Trie_h

#include <vector>
#include <unordered_set>

#include "Constraints.h"

class Trie;
#include "Solver.h"

using std::vector;
using std::unordered_set;

//=================================================================================================

struct VerStart;

struct Hor {
  unsigned parent_hor_ix;
  int parent_ver_ix;
  Hor *parent;
  vector<struct VerStart> vers;

  Hor(unsigned parent_hor_ix_, int parent_ver_ix_, Hor *parent)
  : parent_hor_ix(parent_hor_ix_)
  , parent_ver_ix(parent_ver_ix_)
  , parent(parent)
  , vers()
  {}
};

struct HorStart {
  int tag;
  Hor hor;

  HorStart(
    unsigned tag_,
    unsigned parent_hor_ix,
    unsigned parent_ver_ix,
    Hor *parent
  )
  : tag(tag_), hor(parent_hor_ix, parent_ver_ix, parent)
  {}
};

struct VerStart {
  unsigned tag;
  vector<HorStart> hors;

  VerStart() : hors() {}
};


enum WhatToDo {
  WATCH = -3,
  DONE = -2,
  AGAIN = -1,
  CONFLICT = 0,
  PROPAGATE = 1,
};

class Trie : public Constr {
public:
  Hor root;
  Hor *active_hor;
  unsigned hor_ix = 0;
  int ver_ix = -1;
  unsigned var_count;
  vector<unsigned> back_ptrs;
  unsigned active_var = 0;
  unsigned active_var_old = 0;
  unsigned undo_skip_count = 0;
  vector<unsigned> my_zeroes;

  Trie(unsigned var_count);

  Lit guess(Solver &S);
  void onSat(Solver &S);

  void remove(Solver& S, bool just_dealloc);
  bool simplify(Solver& S);
  bool propagate (Solver& S, Lit p, bool& keep_watch);
  void undo(Solver& S, Lit p);
  void calcReason(Solver& S, Lit p, vec<Lit>& out_reason);

  WhatToDo after_hors_change(Solver &S);
  WhatToDo after_vers_change(Solver &S);
  void back();
};

//=================================================================================================
#endif
