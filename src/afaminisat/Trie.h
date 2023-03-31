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
class HorLine;

extern int hor_head_count;
extern int hor_count;
extern int ver_count;

struct BackJumper {
    HorLine *active_hor;
    unsigned hor_ix;
    int ver_ix;

    BackJumper() {}

    BackJumper
    ( HorLine *active_hor_
    , unsigned hor_ix_
    , int ver_ix_
    )
    : active_hor(active_hor_)
    , hor_ix(hor_ix_)
    , ver_ix(ver_ix_)
    {}

    void jump(Solver &S);
};


struct AccBackJumper {
  bool enabled;
  BackJumper backjumper;

  AccBackJumper() : enabled(false) {}

  void enable
  ( HorLine *active_hor
  , unsigned hor_ix
  , int ver_ix
  ) {
    enabled = true;
    backjumper.active_hor = active_hor;
    backjumper.hor_ix = hor_ix;
    backjumper.ver_ix = ver_ix;
  }
};


struct HorLine {
  HorLine *back_hor;
  unsigned back_hor_ix;
  unsigned back_ver_ix;
  vector<VerHead> elems;
};


class HorHead {
public:
  unsigned tag;
  HorLine *vers;

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
  vector<HorHead> hors;

  VerHead(unsigned tag_) : tag(tag_), hors() {
    if (verbosity >= -2) ver_count++;
  }
  VerHead(VerHead&& old) : tag(old.tag), hors(std::move(old.hors)) {
  }

  ~VerHead() {
    if (verbosity >= -2) ver_count--;
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

struct Place {
  HorLine *active_hor;
  unsigned hor_ix;
  int ver_ix;

  void cut_away();
};

class Trie : public Constr {
public:
  // the underlying automaton
  HorLine root;
  HorLine *active_hor;
  unsigned hor_ix = 0;
  int ver_ix = -1;

  // constant - the number of states of the analysed AFA
  unsigned var_count;

  // There is one back_ptr for each variable (= state of the analysed AFA).
  // If the trie is already in the accepting condition (all places have accepted),
  // undef-valued variables get guessed to 1 and these pointers connect them
  // into a list (where the last element is the firstly guessed variable). When
  // undoing guesses, the list is popped, of course.
  // A back_ptr contains the index of the next list item + 1.
  vector<unsigned> back_ptrs;

  unsigned active_var = 0;
  unsigned active_var_old = 0;
  vector<Place> propagations;  // for calcReason
  PropUndo prop_undo = {};
  ActiveVarDoneUndo active_var_done_undo = {};
  BackJumperUndo backjumper_undo = {};
  vector<AccBackJumper> acc_backjumpers;
  vector<bool> watch_mask;
  vector<BackJumper> backjumpers;
  int last_state_level = -1;
  bool move_right = false;

  Trie(unsigned var_count, int index_count);

  Lit guess(Solver &S);

  // Result: should the trie be cut at the active place's back_ptr?
  bool onSat(Solver &S);
  bool reset(Solver &S);
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


#define ITER_MY_ZEROES(active_hor, hor_ix, ver_ix, x, fn) { \
  unsigned __hix = (hor_ix); \
  int __vix = (ver_ix); \
  for (HorLine *__hor = (active_hor); __hor;) { \
    VerHead &__ver = __hor->elems[__hix]; \
    unsigned x = __ver.tag; \
    {fn} \
    for (unsigned __i = 0; __i < __vix; __i++) { \
      unsigned x = __ver.hors[__i].tag; \
      {fn} \
    } \
    __hix = __hor->back_hor_ix; \
    __vix = __hor->back_ver_ix; \
    __hor = __hor->back_hor; \
  } \
}

//=================================================================================================
#endif
