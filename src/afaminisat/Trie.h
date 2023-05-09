#ifndef Trie_h
#define Trie_h

#include <limits>
#include <vector>
#include <deque>
#include <unordered_set>
#include <fstream>

#include "Constraints.h"

class Solver;

using std::deque;
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
  WhatToDo move_on_propagate(Solver &S, Lit out_lit);
  MultimoveEnd multimove_on_propagate(Solver &S, WhatToDo what_to_do);

  GreaterPlace &save_as_greater(Solver &S);
  bool handle_greater_stack(Solver &S);

  friend std::ostream& operator<<(std::ostream& os, Place const &p);
};

struct PlaceAttrs : Place {
  Solver &S;
  PlaceAttrs(Place p, Solver &_S) : Place(p), S(_S) { };
  friend std::ostream& operator<<(std::ostream& os, PlaceAttrs const &p);
};

struct WatchedPlace : public Place, public virtual Constr {
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

  bool full_multimove_on_propagate(Solver &S, WhatToDo what_to_do);

  bool propagate (Solver& S, Lit p, bool& keep_watch);
  void remove    (Solver& S, bool just_dealloc = false) { };
  bool simplify  (Solver& S) { return false; };
  void calcReason(Solver& S, Lit p, vec<Lit>& out_reason);
  void moveWatch(int i, Lit p);
};


struct BackJumper {
    Place place;

    void jump(Solver &S);
};


struct AccBackJumper : BackJumper {
  bool enabled;

  AccBackJumper() : enabled(false) {}

  void enable(Place place_) {
    enabled = true;
    place = place_;
  }
};


struct GreaterBackjumper;

struct ChangedGreaterPlace {
  Place place;
  GreaterBackjumper *backjumper;
  unsigned backjumper_added_ix;
};

struct GreaterPlace : public WatchedPlace {
  unsigned ix;
  bool enabled = true;
  GreaterBackjumper *backjumper;
  unsigned backjumper_added_ix;
  unsigned previous, next;

  GreaterPlace(HorLine *hor_, unsigned ix_, unsigned previous_);
  GreaterPlace(ChangedGreaterPlace changed_place, unsigned ix_, unsigned previous_);

  void on_accept(Solver &S);
};

struct AddedGreaterPlace {
  unsigned ix;
  bool removed = false;
};


struct GreaterBackjumper : Undoable {
  BackJumper least_backjumper;
  int level = -1;
  vector<AddedGreaterPlace> added_places;
  vector<ChangedGreaterPlace> changed_places;

  GreaterBackjumper(int level_)
  : added_places(), changed_places(), level(level_) {}

  GreaterBackjumper(Place least_place_) noexcept
  : added_places()
  , changed_places()
  , least_backjumper{least_place_}
  {}

  void undo(Solver &S, Lit _p);
};


struct HorLine {
  Place back_ptr;
  vector<VerHead> elems;
};


class HorHead {
public:
  unsigned tag;
  HorLine *hor;

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
  ~RemovedWatch(void) {};
};


struct ActiveVarDoneUndo : public Undoable { void undo(Solver &S, Lit _p); };

extern ActiveVarDoneUndo ACTIVE_VAR_DONE_UNDO;
extern RemovedWatch REMOVED_WATCH;

class Trie : public Undoable, public WatchedPlace {
public:
  // the underlying automaton
  HorLine root;

  deque<GreaterPlace> greater_places;
  vector<int> free_greater_places;
  vector<Place> greater_stack;
  unsigned last_greater = IX_NULL;

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
  vector<AccBackJumper> acc_backjumpers;
  deque<GreaterBackjumper> greater_backjumpers;

  Trie();
  void init(unsigned var_count);

  Lit guess(Solver &S);

  // Result: should the trie be cut at the active place's back_ptr?
  bool onSat(Solver &S);
  bool reset(Solver &S);

  void undo(Solver& S, Lit p);


  // LeastPlace
  int accept_level = -1;
  bool ver_accept = false;
  void on_accept(Solver &S);

  // debugging
  void to_dot(Solver& S, const char *filename);
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
