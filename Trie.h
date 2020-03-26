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

class VerHead;
struct BackJumper;


struct Hor {
  vector<struct VerHead> *vers;
  unsigned topo;
  struct BackJumper *back;

  Hor(unsigned topo_, struct BackJumper *back_)
  : vers(new vector<struct VerHead>()), topo(topo_), back(back_)
  {}

  Hor(Hor&& old) : vers(old.vers), topo(old.topo), back(old.back) {
    old.vers = NULL;
  }

  ~Hor() {
    if (vers) delete vers;
  }
};


struct BackJumper : public Undoable {
    Hor *active_hor;
    unsigned hor_ix;
    int ver_ix;
    unsigned my_zeroes_size;

    BackJumper(Hor *active_hor_, unsigned hor_ix_, int ver_ix_)
    : active_hor(active_hor_), hor_ix(hor_ix_), ver_ix(ver_ix_)
    {}

    void cut();

    void undo(Solver &S, Lit p);
};


class Head {
public:
  unsigned tag;
  BackJumper *backjumper;

  Head(unsigned tag_, Hor *active_hor, unsigned hor_ix, int ver_ix)
  : tag(tag_)
  , backjumper(new BackJumper(active_hor, hor_ix, ver_ix))
  {}

  Head(Head&& old) : tag(old.tag), backjumper(old.backjumper) {
    printf("MOVING Head\n");
    old.backjumper = NULL;
  }

  ~Head() {
    if (backjumper) delete backjumper;
  }
};


class HorHead : public Head {
public:
  Hor *hor;

  HorHead(unsigned tag_, Hor *active_hor, unsigned hor_ix, int ver_ix)
  : Head(tag_, active_hor, hor_ix, ver_ix)
  , hor(new Hor(active_hor->topo + 1, backjumper))
  {}

  HorHead(HorHead&& old) : Head(std::move(old)), hor(old.hor) {
    old.hor = NULL;
  }

  HorHead& operator=(const HorHead&) {
    return *this;  // WARNING: not implemented, only to make vector::erase happy
  }

  ~HorHead() {
    if (hor) delete hor;
  }
};


class VerHead : public Head {
public:
  vector<HorHead> *hors;

  VerHead(unsigned tag_, Hor *active_hor, unsigned hor_ix, int ver_ix)
  : Head(tag_, active_hor, hor_ix, ver_ix)
  , hors(new vector<HorHead>())
  {}

  VerHead(VerHead&& old) : Head(std::move(old)), hors(old.hors) {
    old.hors = NULL;
  }

  ~VerHead() {
    if (hors) delete hors;
  }
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
  vector<unsigned> my_zeroes;
  vector<BackJumper*> propagations;
  int last_state_level = -1;

  Trie(unsigned var_count);

  Lit guess(Solver &S);
  BackJumper* onSat(Solver &S);
  void reset(Solver &S);

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
