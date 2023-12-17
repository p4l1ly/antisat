#ifndef Trie_h
#define Trie_h

#include <limits>
#include <vector>
#include <unordered_set>
#include <utility>
#include <fstream>
#include <stdint.h>

#include "Constraints.h"
#include "LogList.h"

class Solver;

using std::pair;
using std::vector;
using std::unordered_set;

//=================================================================================================

class VerHead;
class HorHead;
struct HorLine;

extern int hor_head_count;
extern int hor_count;
extern int ver_count;

const unsigned IX_NULL = std::numeric_limits<unsigned>::max();


enum WhatToDo {
  WATCH = -3,
  DONE = -2,
  AGAIN = -1,
  EXHAUST = 0,
};

enum MultimoveEnd {
  E_WATCH = -3,
  E_DONE = -2,
  E_EXHAUST = 0,
};


struct RearGuard;
struct VanGuard;
class Trie;

struct Place : public Reason {
public:
  HorLine *hor;
  unsigned hor_ix;
  unsigned ver_ix;

  Place(HorLine *hor_, unsigned hor_ix_, unsigned ver_ix_)
  : hor(hor_), hor_ix(hor_ix_), ver_ix(ver_ix_)
  {}

  void cut_away();
  HorHead &deref_ver() const;
  VerHead &deref_hor() const;
  Lit get_tag() const;
  bool ver_is_last() const;
  bool ver_is_singleton() const;
  bool is_ver() const;
  bool in_exhaust() const;
  HorHead &get_leftmost(Trie &trie) const;
  void set_van_visit_level(int level, VanGuard &van);
  void set_rear_visit_level(int level, RearGuard &rear);
  int get_depth_if_valid(Trie &trie) const;

  friend std::ostream& operator<<(std::ostream& os, Place const &p);

  void calcReason(Solver& S, Lit p, vec<Lit>& out_reason);
};

struct PlaceAttrs : Place {
  Solver &S;
  PlaceAttrs(Place p, Solver &_S) : Place(p), S(_S) { };
  friend std::ostream& operator<<(std::ostream& os, PlaceAttrs const &p);
};

struct WatchedPlace : public Place, public Constr {
public:

#ifdef MY_DEBUG
  int watch_ix_pos = -1;
  int watch_ix_neg = -1;
#else
  int watch_ix_pos;
  int watch_ix_neg;
#endif

  WatchedPlace(Place place);

  void set_watch(Solver &S);
  void remove_watch(Solver &S, Lit old_tag);
  void remove_watch_pos(Solver &S, Lit lit);
  void remove_watch_neg(Solver &S, Lit lit);

  void remove    (Solver& S, bool just_dealloc = false) { };
  bool simplify  (Solver& S) { return false; };
  void moveWatch(int i, Lit p);
};

struct RearSnapshot {
  RearGuard *ix;
  Place place;
  int last_change_level;
  Place accepting_place;
};

struct VanSnapshot {
  VanGuard *ix;
  Place place;
  int last_change_level;
  RearGuard *rear;
};

struct RearGuard : public WatchedPlace {
  bool enabled;
  int last_change_level;
  RearGuard *previous, *next;
  VanGuard *last_van;

  Place accepting_place;
  VanGuard *accepting_reusable_van;

  RearGuard(
    Place place,
    int last_change_level_,
    RearGuard *previous_,
    bool enabled_
  )
  : WatchedPlace(place)
  , last_change_level(last_change_level_)
  , previous(previous_)
  , next(NULL)
  , enabled(enabled_)
  , last_van(NULL)
  , accepting_place(NULL, 0, 0)
  { }

  void on_accept_rear(Solver &S);
  void on_accept_van(Solver &S);

  Place* jump(Solver &S);
  Reason* propagate(Solver& S, Lit p, bool& keep_watch);

  void make_snapshot(Solver &S);
};

struct VanGuard : public WatchedPlace {
  RearGuard *rear;
  bool enabled;
  int last_change_level;
  VanGuard *previous, *next;

  VanGuard(Place place, RearGuard* rear_guard_, int last_change_level_, bool enabled_)
  : WatchedPlace(place)
  , rear(rear_guard_)
  , last_change_level(last_change_level_)
  , enabled(enabled_)
  , previous(NULL)
  , next(NULL)
  {
    if (enabled_) {
      VanGuard *pre = rear->last_van;
      if (pre) pre->next = this;
      previous = pre;
      rear->last_van = this;
    }
  }

  void on_accept(Solver &S);
  Place* on_exhaust(Solver &S);
  Place* full_multimove_on_propagate(Solver &S, WhatToDo what_to_do);
  Reason* propagate(Solver& S, Lit p, bool& keep_watch);

  void make_snapshot(Solver &S, int level);

  void branch(Solver &S);
  WhatToDo after_hors_change(Solver &S);
  WhatToDo after_vers_change(Solver &S);
  WhatToDo move_on_propagate(Solver &S, Lit out_lit, bool do_branch);
  MultimoveEnd multimove_on_propagate(Solver &S, WhatToDo what_to_do);
};

struct Snapshot {
  bool is_acc;
  LogList<RearGuard> new_rears;
  LogList<VanGuard> new_vans;
  vector<RearSnapshot> rear_snapshots;
  vector<VanSnapshot> van_snapshots;
  LogList<Place> reasons;
  vector<Place> cuts;

  Place accepting_place;

  Snapshot()
  : new_rears()
  , new_vans()
  , rear_snapshots()
  , van_snapshots()
  , reasons()
  , cuts()
  // IX_NULL in hor_ix means no change. If hor==NULL and hor_ix==0, it means that
  // trie.accepting_place should be cleared.
  , accepting_place(NULL, IX_NULL, 0)
  {}

  Snapshot(Snapshot&& old) noexcept
  : new_rears(std::move(old.new_rears))
  , new_vans(std::move(old.new_vans))
  , rear_snapshots(std::move(old.rear_snapshots))
  , van_snapshots(std::move(old.van_snapshots))
  , is_acc(old.is_acc)
  , accepting_place(old.accepting_place)
  , reasons(std::move(old.reasons))
  , cuts(std::move(old.cuts))
  {}

  Snapshot(Snapshot& old) = delete;
};


struct HorLine {
  Place back_ptr;
  vector<VerHead> elems;
};


class HorHead {
public:
  Lit tag;
  HorLine *hor;

  int depth;
  bool is_under_cut = false;
  int van_visit_level;
  int rear_visit_level;
  RearGuard *van_visit_rear;
  VanGuard *van_visit_van;
  RearGuard *rear_visit_rear;

  HorHead(
    Lit tag_,
    int depth_,
    int van_visit_level_,
    int rear_visit_level_,
    RearGuard *van_visit_rear_,
    VanGuard *van_visit_van_,
    RearGuard *rear_visit_rear_
  )
  : tag(tag_)
  , hor(NULL)
  , depth(depth_)
  , van_visit_level(van_visit_level_)
  , rear_visit_level(rear_visit_level_)
  , van_visit_rear(van_visit_rear_)
  , van_visit_van(van_visit_van_)
  , rear_visit_rear(rear_visit_rear_)
  {
    if (verbosity >= -2) hor_head_count++;
  }

  HorHead(
    Lit tag_,
    int depth_
  )
  : tag(tag_)
  , hor(NULL)
  , depth(depth_)
  , van_visit_level(0)
  , rear_visit_level(0)
  , van_visit_rear(NULL)
  , van_visit_van(NULL)
  , rear_visit_rear(NULL)
  {
    if (verbosity >= -2) hor_head_count++;
  }

  HorHead& operator=(const HorHead&) {
    assert(false);
    return *this;
  }

  ~HorHead() {
    if (verbosity >= -2) hor_head_count--;
    if (hor) {
      if (verbosity >= -2) hor_count--;
      delete hor;
    }
  }
};


class VerHead {
public:
  Lit tag;
  vector<HorHead> hors;

  VerHead(Lit tag_) : tag(tag_), hors() {
    if (verbosity >= -2) ver_count++;
  }
  VerHead(VerHead&& old) noexcept
  : tag(old.tag), hors(std::move(old.hors)) {
    if (verbosity >= -2) ver_count++;
  }

  ~VerHead() {
    if (verbosity >= -2) ver_count--;
  }
};


struct RemovedWatch : public Constr {
  void remove    (Solver& S, bool just_dealloc = false) { };
  Reason* propagate (Solver& S, Lit p, bool& keep_watch) { return NULL; };
  bool simplify(Solver& S) { return false; };
  void moveWatch(int i, Lit p) {};
};


enum Mode { clauses, branch_always };

extern RemovedWatch REMOVED_WATCH;
extern Mode TRIE_MODE;

struct StackItem {
  HorLine* hor;
  unsigned hor_ix;
  Place *handle(Solver &S, RearGuard &rear);
};

class Trie : public Undoable {
public:
  // the underlying automaton
  HorLine root;
  HorHead root_leftmost;

  LogList<RearGuard> root_new_rears;
  LogList<VanGuard> root_new_vans;
  LogList<Place> root_reasons;
  vector<StackItem> stack;
  RearGuard *last_rear = NULL;

  // constant - the number of states of the analysed AFA
  vector<Lit> my_literals;

  // There is one back_ptr for each variable (= state of the analysed AFA).
  // If the trie is already in the accepting condition (all places have accepted),
  // undef-valued variables get guessed to 1 and these pointers connect them
  // into a list (where the last element is the firstly guessed variable). When
  // undoing guesses, the list is popped, of course.
  // A back_ptr contains the index of the next list item + 1.
  vector<unsigned> back_ptrs;

  unsigned active_var = 0;
  unsigned active_var_old = 0;

  unsigned snapshot_count = 0;
  std::vector<Snapshot> snapshots;

  Place accepting_place;

  Snapshot &get_last_snapshot() { return snapshots[snapshot_count - 1]; }
  Snapshot& new_snapshot();
  void make_accepting_snapshot(Solver &S);

  vector<Place> root_cuts;

  Trie();
  bool init(const vec<Lit>& my_literals, const unordered_set<unsigned>& init_clause_omits);

  bool guess(Solver &S);

  // Result: should the trie be cut at the active place's back_ptr?
  void onSat(Solver &S);
  Place* reset(Solver &S);

  void undo(Solver& S);

  // debugging
  void to_dot(Solver& S, const char *filename);
  void print_places();

  // private
  void onSatSnapshots(
    unsigned i,
    unsigned &last_i_rear,
    unsigned &last_i_van,
    HorLine *extended_hor,
    unsigned extended_hor_ix,
    int lvl,
    Snapshot &snapshot,
    VanGuard *vguard,
    RearGuard *rguard,
    VanSnapshot *&next_snapshot_van,
    RearSnapshot *&next_snapshot_rear,
    vector<std::pair<int, Lit>> &added_vars,
    RearGuard *leftmost_van_visit_rear,
    int leftmost_rear_visit_level,
    int leftmost_van_visit_level
  );
};


#define ITER_MY_ZEROES(place, x, fn) { \
  unsigned __hix = ((place).hor_ix); \
  int __vix = ((place).ver_ix); \
  for (HorLine *__hor = ((place).hor); __hor;) { \
    VerHead &__ver = __hor->elems[__hix]; \
    if (__vix >= 0) { \
      Lit x = __ver.tag; \
      {fn} \
      for (unsigned __i = 0; __i < __vix; __i++) { \
        Lit x = __ver.hors[__i].tag; \
        {fn} \
      } \
    } \
    __hix = __hor->back_ptr.hor_ix; \
    __vix = __hor->back_ptr.ver_ix; \
    __hor = __hor->back_ptr.hor; \
  } \
}

//=================================================================================================
#endif
