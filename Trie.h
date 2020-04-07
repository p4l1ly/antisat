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

extern int hor_head_count;
extern int hor_count;
extern int ver_count;

struct Knee {
  vector<VerHead> *active_hor;
  unsigned hor_ix;
  unsigned ver_ix;

  Knee() {}

  Knee
  ( vector<VerHead> *active_hor_
  , unsigned hor_ix_
  , int ver_ix_
  )
  : active_hor(active_hor_)
  , hor_ix(hor_ix_)
  , ver_ix(ver_ix_)
  {}

  void cut();
};

struct CutKnee {
  bool enabled;
  Knee knee;

  CutKnee() : enabled(false) {}

  CutKnee(Knee &knee_)
  : enabled(true), knee(knee_.active_hor, knee_.hor_ix, knee_.ver_ix)
  {}
};

struct BackJumper {
    vector<VerHead> *active_hor;
    unsigned hor_ix;
    int ver_ix;
    unsigned my_zeroes_size;
    unsigned knees_size;

    BackJumper() {}

    BackJumper
    ( vector<VerHead> *active_hor_
    , unsigned hor_ix_
    , int ver_ix_
    , unsigned my_zeroes_size_
    , unsigned knees_size_
    )
    : active_hor(active_hor_)
    , hor_ix(hor_ix_)
    , ver_ix(ver_ix_)
    , my_zeroes_size(my_zeroes_size_)
    , knees_size(knees_size_)
    {}

    void jump(Solver &S);
};


struct AccBackJumper {
  bool enabled;
  BackJumper backjumper;

  AccBackJumper() : enabled(false) {}

  void enable
  ( vector<VerHead> *active_hor
  , unsigned hor_ix
  , int ver_ix
  , unsigned my_zeroes_size
  , unsigned knees_size
  ) {
    enabled = true;
    backjumper.active_hor = active_hor;
    backjumper.hor_ix = hor_ix;
    backjumper.ver_ix = ver_ix;
    backjumper.my_zeroes_size = my_zeroes_size;
    backjumper.knees_size = knees_size;
  }
};


class HorHead {
public:
  unsigned tag;
  vector<VerHead> *vers;

  HorHead(unsigned tag_) : tag(tag_), vers(NULL) {
    if (verbosity >= -2) hor_head_count++;
  }
  HorHead(HorHead&& old) : tag(old.tag), vers(old.vers) {
    old.vers = NULL;
    if (verbosity >= -2) hor_head_count++;
  }

  HorHead& operator=(const HorHead&) {
    return *this;  // WARNING: not implemented, only to make vector::erase happy
  }

  ~HorHead() {
    if (verbosity >= -2) hor_head_count--;
    if (vers) {
      if (verbosity >= -2) hor_count--;
      delete vers;
    }
  }
};


class VerHead {
public:
  unsigned tag;
  vector<HorHead> *hors;

  VerHead(unsigned tag_) : tag(tag_), hors(new vector<HorHead>()) {
    if (verbosity >= -2) ver_count++;
  }
  VerHead(VerHead&& old) : tag(old.tag), hors(old.hors) {
    if (verbosity >= -2) ver_count++;
    old.hors = NULL;
  }

  ~VerHead() {
    if (verbosity >= -2) ver_count--;
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


struct PropUndo : public Undoable { void undo(Solver &S, Lit _p); };
struct ActiveVarDoneUndo : public Undoable { void undo(Solver &S, Lit _p); };
struct BackJumperUndo : public Undoable { void undo(Solver &S, Lit _p); };


class Trie : public Constr {
public:
  vector<VerHead> root;
  vector<VerHead> *active_hor;
  unsigned hor_ix = 0;
  int ver_ix = -1;
  unsigned var_count;
  vector<unsigned> back_ptrs;
  unsigned active_var = 0;
  unsigned active_var_old = 0;
  vector<unsigned> my_zeroes;
  vector<unsigned> propagations;
  PropUndo prop_undo = {};
  ActiveVarDoneUndo active_var_done_undo = {};
  BackJumperUndo backjumper_undo = {};
  vector<AccBackJumper> acc_backjumpers;
  vector<bool> watch_mask;
  vector<BackJumper> backjumpers;
  vector<Knee> knees;
  int last_state_level = -1;
  bool move_right = false;

  Trie(unsigned var_count, int index_count);

  Lit guess(Solver &S);
  CutKnee onSat(Solver &S);
  void reset(Solver &S);
  void watch(Solver &S, int var_);

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
