#ifndef Trie_h
#define Trie_h

#include <limits>
#include <vector>
#include <deque>
#include <unordered_set>
#include <utility>
#include <fstream>
#include <stdint.h>

#include "Constraints.h"
#include "LogList.h"

class Solver;

using std::deque;
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
  E_PROPAGATE = 1,
};


struct GreaterPlace;

struct Place {
public:
  HorLine *hor;
  unsigned hor_ix;
  unsigned ver_ix;

  void cut_away();
  HorHead &deref_ver() const;
  VerHead &deref_hor() const;
  unsigned get_tag() const;
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

  WatchedPlace(HorLine *hor_);
  WatchedPlace(Place place);

  void set_watch(Solver &S);
  void remove_watch(Solver &S, unsigned old_tag);
  void remove_watch_pos(Solver &S, Lit lit);
  void remove_watch_neg(Solver &S, Lit lit);

  virtual void on_accept(Solver &S) = 0;
  virtual GreaterIx my_greater_ix() = 0;

  void accept_notify_horhead(Solver& S);
  bool full_multimove_on_propagate(Solver &S, WhatToDo what_to_do);

  bool propagate (Solver& S, Lit p, bool& keep_watch);
  void remove    (Solver& S, bool just_dealloc = false) { };
  bool simplify  (Solver& S) { return false; };
  void calcReason(Solver& S, Lit p, vec<Lit>& out_reason);
  void moveWatch(int i, Lit p);
};


struct GreaterBackjumper;

struct ChangedGreaterPlace {
  Place place;
  GreaterIx ix;
  GreaterBackjumper *last_change_backjumper;
};

struct GreaterPlace : public WatchedPlace {
  GreaterIx ix;
  bool enabled = true;
  GreaterBackjumper *last_change_backjumper;
  GreaterIx previous, next;

  GreaterIx swallow_ix;
  int swallow_level;

  GreaterPlace(ChangedGreaterPlace changed_place, GreaterIx previous_);
  bool propagate (Solver& S, Lit p, bool& keep_watch);

  void on_accept(Solver &S);
  GreaterIx my_greater_ix() { return ix; }
};

struct GreaterBackjumper : Undoable {
  Place least_place;
  bool least_enabled;
  int level;
  LogList<GreaterPlace> greater_places;
  vector<ChangedGreaterPlace> changed_places;

  GreaterBackjumper(int level_)
  : greater_places()
  , changed_places()
  , level(level_)
  , least_enabled(false)
  {}

  GreaterBackjumper(Place least_place_, int level_) noexcept
  : greater_places()
  , changed_places()
  , level(level_)
  , least_place{least_place_}
  , least_enabled(true)
  {}

  GreaterBackjumper(GreaterBackjumper&& old) noexcept
  : least_place(old.least_place)
  , least_enabled(old.least_enabled)
  , level(old.level)
  , greater_places(std::move(old.greater_places))
  , changed_places(std::move(old.changed_places)) {
  }

  GreaterBackjumper(GreaterBackjumper& old) = delete;

  void undo(Solver &S, Lit _p);

  void jump_least(Solver &S);
};


struct HorLine {
  Place back_ptr;
  vector<VerHead> elems;
};


class HorHead {
public:
  unsigned tag;
  HorLine *hor;

  GreaterIx accept_ix;
  int accept_level;

  HorHead(unsigned tag_) : tag(tag_), hor(NULL) {
    if (verbosity >= -2) hor_head_count++;
  }
  HorHead(HorHead&& old) noexcept : tag(old.tag), hor(old.hor) {
    old.hor = NULL;
    if (verbosity >= -2) hor_head_count++;
  }

  HorHead& operator=(const HorHead&) {
    return *this;  // WARNING: not implemented, only to make vector::erase happy
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
  unsigned tag;
  GreaterIx greater_ix;
  vector<HorHead> hors;

  VerHead(unsigned tag_) : tag(tag_), hors() {
    if (verbosity >= -2) ver_count++;
  }
  VerHead(VerHead&& old) noexcept : tag(old.tag), hors(std::move(old.hors)) {
  }

  ~VerHead() {
    if (verbosity >= -2) ver_count--;
  }
};


struct RemovedWatch : public Constr {
  void remove    (Solver& S, bool just_dealloc = false) { };
  bool propagate (Solver& S, Lit p, bool& keep_watch) { return true; };
  bool simplify  (Solver& S) { return false; };
  void calcReason(Solver& S, Lit p, vec<Lit>& out_reason) { };
  void moveWatch(int i, Lit p) {};
};


struct ActiveVarDoneUndo : public Undoable { void undo(Solver &S, Lit _p); };
enum Mode { clauses, dnf, branch_on_zero, branch_always };

extern ActiveVarDoneUndo ACTIVE_VAR_DONE_UNDO;
extern RemovedWatch REMOVED_WATCH;
extern Mode TRIE_MODE;

struct GreaterStackItem {
  HorLine* hor;
  unsigned hor_ix;
  bool handle(Solver &S);
};

class Trie : public Undoable, public WatchedPlace {
public:
  // the underlying automaton
  HorLine root;

  GreaterIx root_accept_ix = GREATER_IX_NULL;
  int root_accept_level = -1;

  LogList<GreaterPlace> root_greater_places;
  vector<GreaterStackItem> greater_stack;
  GreaterIx last_greater = pair(IX_NULL, IX32_NULL);

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
  deque<GreaterBackjumper> greater_backjumpers;

  Place to_cut;

  Trie();
  void init(unsigned var_count);

  Lit guess(Solver &S);

  // Result: should the trie be cut at the active place's back_ptr?
  void onSat(Solver &S);
  bool reset(Solver &S);

  void undo(Solver& S, Lit p);


  // LeastPlace
  bool ver_accept = false;
  void on_accept(Solver &S);
  GreaterIx my_greater_ix() { return GREATER_IX_NULL; }

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
      unsigned x = __ver.tag; \
      {fn} \
      for (unsigned __i = 0; __i < __vix; __i++) { \
        unsigned x = __ver.hors[__i].tag; \
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
