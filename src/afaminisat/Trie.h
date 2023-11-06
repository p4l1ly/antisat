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

typedef pair<unsigned, uint32_t> GreaterIx;

const unsigned IX_NULL = std::numeric_limits<unsigned>::max();
const unsigned IX32_NULL = std::numeric_limits<uint32_t>::max();
const GreaterIx GREATER_IX_NULL = pair(IX_NULL, IX32_NULL);
const GreaterIx GREATER_IX_FIRST = pair(IX_NULL, 0);


enum WhatToDo {
  WATCH = -3,
  DONE = -2,
  AGAIN = -1,
  CONFLICT = 0,
  PROPAGATE = 1,
};

enum MultimoveEnd {
  E_WATCH = -3,
  E_DONE = -2,
  E_CONFLICT = 0,
};


struct GreaterPlace;

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
  bool hor_is_out() const;
  bool ver_is_last() const;
  bool ver_is_singleton() const;
  bool is_ver() const;
  bool in_conflict() const;

  void branch(Solver &S);
  WhatToDo after_hors_change(Solver &S);
  WhatToDo after_vers_change(Solver &S);
  WhatToDo move_on_propagate(Solver &S, Lit out_lit, bool do_branch);
  MultimoveEnd multimove_on_propagate(Solver &S, WhatToDo what_to_do);

  GreaterPlace &save_as_greater(Solver &S, bool enabled = true);

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
  int watch_ix_pos;
  int watch_ix_neg;

  WatchedPlace(Place place);

  void set_watch(Solver &S);
  void remove_watch(Solver &S, Lit old_tag);
  void remove_watch_pos(Solver &S, Lit lit);
  void remove_watch_neg(Solver &S, Lit lit);

  virtual void on_accept(Solver &S) = 0;
  virtual GreaterIx my_greater_ix() = 0;

  void accept_notify_horhead(Solver& S);
  Reason* full_multimove_on_propagate(Solver &S, WhatToDo what_to_do);

  Reason* propagate (Solver& S, Lit p, bool& keep_watch);
  void remove    (Solver& S, bool just_dealloc = false) { };
  bool simplify  (Solver& S) { return false; };
  void moveWatch(int i, Lit p);
};


struct ChangedGreaterPlace {
  Place place;
  GreaterIx ix;
  int last_change_level;
};

struct GreaterPlace : public WatchedPlace {
  GreaterIx ix;
  bool enabled = true;
  int last_change_level;
  GreaterIx previous, next;

  GreaterPlace(ChangedGreaterPlace changed_place, GreaterIx previous_);
  GreaterPlace(ChangedGreaterPlace changed_place, GreaterIx previous_, bool enabled_);
  Reason* propagate (Solver& S, Lit p, bool& keep_watch);

  void on_accept(Solver &S);
  GreaterIx my_greater_ix() { return ix; }
  void onSat(Solver &S, int accept_level);
};

struct GreaterBackjumper {
  bool is_acc;
  LogList<GreaterPlace> greater_places;
  vector<ChangedGreaterPlace> changed_places;
  LogList<Place> reasons;

  int accept_depth = -2;
  int accept_level = -1;
  GreaterPlace *accept_place = NULL;

  GreaterBackjumper() : greater_places(), changed_places() {}

  GreaterBackjumper(GreaterBackjumper&& old) noexcept
  : greater_places(std::move(old.greater_places))
  , changed_places(std::move(old.changed_places))
  , is_acc(old.is_acc)
  , accept_depth(old.accept_depth)
  , accept_level(old.accept_level)
  , accept_place(old.accept_place)
  , reasons(std::move(old.reasons))
  {}

  GreaterBackjumper(GreaterBackjumper& old) = delete;
};


struct HorLine {
  Place back_ptr;
  vector<VerHead> elems;
};


class HorHead {
public:
  Lit tag;
  HorLine *hor;

  int accept_level;
  int visit_level;
  int depth;

  HorHead(Lit tag_, int visit_level_, int depth_)
  : tag(tag_), hor(NULL), visit_level(visit_level_), depth(depth_)
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
  GreaterIx greater_ix;
  vector<HorHead> hors;

  VerHead(Lit tag_) : tag(tag_), hors() {
    if (verbosity >= -2) ver_count++;
  }
  VerHead(VerHead&& old) noexcept
  : tag(old.tag), greater_ix(old.greater_ix), hors(std::move(old.hors)) {
    if (verbosity >= -2) ver_count++;
  }

  ~VerHead() {
    if (verbosity >= -2) ver_count--;
  }
};


struct RemovedWatch : public Constr {
  void remove    (Solver& S, bool just_dealloc = false) { };
  Reason* propagate (Solver& S, Lit p, bool& keep_watch) { return NULL; };
  bool simplify  (Solver& S) { return false; };
  void moveWatch(int i, Lit p) {};
};


enum Mode { clauses, branch_always };

extern RemovedWatch REMOVED_WATCH;
extern Mode TRIE_MODE;

struct GreaterStackItem {
  HorLine* hor;
  unsigned hor_ix;
  bool handle(Solver &S);
};

class Trie : public Undoable {
public:
  // the underlying automaton
  HorLine root;

  LogList<GreaterPlace> root_greater_places;
  LogList<Place> root_reasons;
  vector<GreaterStackItem> greater_stack;
  GreaterIx last_greater = pair(IX_NULL, IX32_NULL);

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

  unsigned backjumper_count = 0;
  std::vector<GreaterBackjumper> greater_backjumpers;

  int accept_depth = -1;
  int accept_level = -1;
  GreaterPlace *accept_place = NULL;

  GreaterBackjumper &get_last_backjumper() {
    return greater_backjumpers[backjumper_count - 1];
  }

  GreaterBackjumper& new_backjumper();

  Place to_cut;

  Trie();
  bool init(const vec<Lit>& my_literals, const unordered_set<unsigned>& init_clause_omits);

  bool guess(Solver &S);

  // Result: should the trie be cut at the active place's back_ptr?
  void onSat(Solver &S);
  Reason* reset(Solver &S);

  void undo(Solver& S);

  GreaterPlace& greater_place_at(GreaterIx ix);

  // debugging
  void to_dot(Solver& S, const char *filename);
  void print_places();
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
