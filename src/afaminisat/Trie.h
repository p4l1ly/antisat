#ifndef Trie_h
#define Trie_h

#include <limits>
#include <vector>
#include <unordered_set>
#include <utility>
#include <fstream>
#include <map>
#include <stdint.h>

#include "Constraints.h"
#include "LogList.h"

class Solver;

using std::pair;
using std::vector;
using std::unordered_set;
using std::map;

//=================================================================================================

struct Head;
const unsigned IX_NULL = std::numeric_limits<unsigned>::max();


enum WhatToDo {
  WATCH,
  DONE,
  EXHAUST,
  RIGHT_VER,
  RIGHT_HOR,
  DOWN_VER,
  DOWN_HOR
};

enum MultimoveEnd {
  E_WATCH = -3,
  E_DONE = -2,
  E_EXHAUST = 0,
};


class Trie;

struct HeadAttrs {
  Head *head;
  Solver &S;
  HeadAttrs(Head *p, Solver &_S) : head(p), S(_S) { };
  friend std::ostream& operator<<(std::ostream& os, HeadAttrs const &p);
};

struct DotHead {
  Head *head;
  Solver &S;
  DotHead(Head *p, Solver &_S) : head(p), S(_S) { };
  friend std::ostream& operator<<(std::ostream& os, DotHead const &p);
};

struct MinusSnapshot {
  Head *place;

  void undo(Solver &S);
};

struct PlusSnapshot {
  Head *place;
  int last_change_level;
  Head *dual;  // Rears have no duals in snapshots, so this implies is_van.
  MinusSnapshot *minus_snapshot;
};

struct Snapshot {
  LogList<PlusSnapshot> plus_snapshots;
  LogList<MinusSnapshot> minus_snapshots;

  Snapshot()
  : plus_snapshots()
  , minus_snapshots()
  {}

  Snapshot(Snapshot&& old) noexcept
  : plus_snapshots(std::move(old.plus_snapshots))
  , minus_snapshots(std::move(old.minus_snapshots))
  {}

  Snapshot(Snapshot& old) = delete;
};


enum GuardType { DANGLING_GUARD, VAN_GUARD, REAR_GUARD, SOLO_GUARD };

struct Guard {
  GuardType guard_type;
  int last_change_level;
  Head *dual;
  Head *previous, *next;
  MinusSnapshot *minus_snapshot;

  void init(
    GuardType guard_type_,
    Head* dual_,
    int last_change_level_,
    MinusSnapshot *msnap_
  ) {
    guard_type = guard_type_;
    dual = dual_;
    last_change_level = last_change_level_;
    previous = NULL;
    next = NULL;
    minus_snapshot = msnap_;
  }

  void untangle();
};


class MultimoveCtx {
public:
  vec<char> &assigns;
  vector<pair<Head*, WhatToDo>> stack;

  MultimoveCtx(vec<char> &assigns_) : assigns(assigns_) {}

  pair<Head*, WhatToDo> move_down_ver(Head* x);
  pair<Head*, WhatToDo> move_down_hor(Head* x);
  pair<Head*, WhatToDo> move_right_ver(Head* x);
  pair<Head*, WhatToDo> move_right_hor(Head* x);

  pair<Head*, WhatToDo> move_right(Head* x);
  pair<Head*, WhatToDo> move_down(Head* x);

  void branch_ver(Head* x);
  void branch_hor(Head* x);

  WhatToDo after_right(Head* x);
  WhatToDo after_down(Head* x);

  pair<Head *, MultimoveEnd> multimove(pair<Head *, WhatToDo> move);
  pair<Head *, MultimoveEnd> first(pair<Head *, WhatToDo> move);
  pair<Head *, MultimoveEnd> next();
  pair<Head *, MultimoveEnd> first_solo(pair<Head *, WhatToDo> move, Solver &S);
  pair<Head *, MultimoveEnd> next_solo(Solver &S);
};


struct Head : public Reason, public Constr {
public:
  // Constant fields.
  Lit tag;
  bool is_ver;
  Head *next;
  Head *dual_next;
  Head *above;
  unsigned external;
  unsigned depth;

  // Dynamic fields.
  bool watching = false;

  // Guard's fields.
  Guard guard;

  Head()
  : tag(lit_Undef)
  , is_ver(true)
  , next(NULL)
  , dual_next(NULL)
  , above(NULL)
  , external(0)
  , depth(0)
  , watching(false)
  , guard()
  { }

  Head(Lit tag_)
  : tag(tag_)
  , is_ver(false)
  , next(NULL)
  , dual_next(NULL)
  , above(NULL)
  , external(0)
  , depth(0)
  , watching(false)
  , guard()
  { }

  Head(Head&& old) noexcept
  : tag(old.tag)
  , is_ver(old.is_ver)
  , next(old.next)
  , dual_next(old.dual_next)
  , above(old.above)
  , external(old.external)
  , depth(old.depth)
  , watching(old.watching)
  , guard(old.guard)
  { }

  Head& operator=(const Head&) {
    assert(false);
    exit(1);
    return *this;
  }

  friend std::ostream& operator<<(std::ostream& os, Head const &p);
  void calcReason(Solver& S, Lit p, vec<Lit>& out_reason);
  void *getSpecificPtr() { return this; }

  void set_watch(Solver &S);
  void unset_watch(Solver &S);

  void remove    (Solver& S, bool just_dealloc = false) { };
  bool simplify  (Solver& S) { return false; };


  Head* full_multimove_on_propagate(
    Solver &S,
    WhatToDo what_to_do,
    MinusSnapshot *msnap,
    Head *rear,
    Head *gprev,
    Head *gnext
  );
  Head* full_multimove_on_propagate_solo(
    Solver &S,
    WhatToDo what_to_do,
    MinusSnapshot *msnap
  );
  GClause propagate(Solver& S, Lit p, bool& keep_watch);

  Head* jump(Solver &S);

  void make_rear_psnap(Solver &S);
  void make_van_psnap(Solver &S, int level);
  void *getSpecificPtr2() { return this; }
  MinusSnapshot *save_to_msnap(Trie &trie, MinusSnapshot *msnap);

  unsigned count();
  Head* solidify();
};


enum Mode { clauses, branch_always };
extern Mode TRIE_MODE;

struct Horline {
  Head** ptr_to_first;
  Head* above;
  vector<Head> elems;

  Horline(Head** ptr_to_first_, Head *above_) : ptr_to_first(ptr_to_first_), above(above_) {}
};

class Trie : public Undoable {
public:
  // the underlying automaton
  Head* root;

  LogList<MinusSnapshot> root_minus_snapshots;

  MultimoveCtx multimove_ctx;
  MultimoveCtx multimove_ctx2;

  // There is one back_ptr for each variable (= state of the analysed AFA).
  // If the trie is already in the accepting condition (all places have accepted),
  // undef-valued variables get guessed to 1 and these pointers connect them
  // into a list (where the last element is the firstly guessed variable). When
  // undoing guesses, the list is popped, of course.
  // A back_ptr contains the index of the next list item + 1.
  unsigned snapshot_count = 0;
  std::vector<Snapshot> snapshots;

  Snapshot &get_last_snapshot() { return snapshots[snapshot_count - 1]; }
  Snapshot& new_snapshot();

  Trie(vec<char> &assigns) : root(NULL), multimove_ctx(assigns), multimove_ctx2(assigns) {}

  Head* reset(Solver &S);

  void undo(Solver& S);

  // debugging
  unsigned count();
  Head* solidify();
  void to_dot(Solver& S, const char *filename);
  void print_guards(Solver& S);

  // manual creation
  bool add_clause(
    vector<Lit> &lits,
    Solver &S,
    unsigned clause_count,
    vector<unsigned> sharing_set,
    vector<Horline> &horlines,
    vector<Head*> &verlines
  );
};

//=================================================================================================
#endif
