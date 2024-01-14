/**************************************************************************************************
MiniSat -- Copyright (c) 2003-2005, Niklas Een, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#ifndef Constraints_h
#define Constraints_h

#include <vector>
#include <cstdio>

#include "SolverTypes.h"
#include "SupQ.h"
#include "Global.h"


//=================================================================================================
// Constraint abstraction:


class Solver;

struct Undoable {
    virtual void undo      (Solver& S) = 0;

    virtual ~Undoable(void) { };  // (not used, just to keep the compiler happy)
};

struct Reason {
    virtual void calcReason(Solver& S, Lit p, vec<Lit>& out_reason) = 0;
    virtual void *getSpecificPtr() = 0;

    virtual ~Reason(void) { };  // (not used, just to keep the compiler happy)
};

// Either a pointer to a clause or a literal.
class GClause {
    void*   data;
    GClause(void* d) : data(d) {}
public:
    friend GClause GClause_new(Lit p);
    friend GClause GClause_new(Reason* c);

    bool        isLit    () const { return ((uintp)data & 1) == 1; }
    Lit         lit      () const { return toLit(((intp)data) >> 1); }
    Reason*     clause   () const { return (Reason*)data; }
    bool        operator == (GClause c) const { return data == c.data; }
    bool        operator != (GClause c) const { return data != c.data; }
};
inline GClause GClause_new(Lit p)     { return GClause((void*)(((intp)index(p) << 1) + 1)); }
inline GClause GClause_new(Reason* c) { assert(((uintp)c & 1) == 0); return GClause((void*)c); }

#define GClause_NULL GClause_new((Clause*)NULL)

struct Constr {
    virtual void remove    (Solver& S, bool just_dealloc = false) = 0;
    virtual GClause propagate (Solver& S, Lit p, bool& keep_watch) = 0;    // ('keep_watch' is set to FALSE beftore call to this method)
    virtual bool simplify  (Solver& S) { return false; };
    virtual void moveWatch(int i, Lit p) = 0;
    virtual void *getSpecificPtr2() = 0;

    virtual ~Constr(void) { };  // (not used, just to keep the compiler happy)
};


//=================================================================================================
// Clauses:


class Clause : public Constr, public Reason {
    unsigned    size_learnt;
    Lit         data[0];

public:
    int  size        (void)      const { return size_learnt >> 1; }
    bool learnt      (void)      const { return size_learnt & 1; }

    void *getSpecificPtr() { return this; }
    void *getSpecificPtr2() { return this; }

    // Constructor -- creates a new clause and add it to watcher lists.
    friend bool Clause_new(Solver& S, const vec<Lit>& ps, bool learnt, Clause*& out_clause);
    friend bool Clause_new_handleConflict(Solver& S, vec<Lit>& ps, Clause*& out_clause);

    // Learnt clauses only:
    bool    locked  (const Solver& S) const;
    float&  activity(void) const {
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wstrict-aliasing"
      return *((float*)&data[size()]);
#pragma GCC diagnostic pop
    }

    // Constraint interface:
    void remove    (Solver& S, bool just_dealloc = false);
    GClause propagate (Solver& S, Lit p, bool& keep_watch);
    bool simplify  (Solver& S);
    void calcReason(Solver& S, Lit p, vec<Lit>& out_reason);
    void moveWatch(int i, Lit p);
};


class UpwardClause : public Constr, public Reason {
    unsigned    size;
    Lit         output = lit_Undef;
    Lit         data[0];

public:
    Lit  operator [] (int index) const { return data[index]; }

    void *getSpecificPtr() { return this; }
    void *getSpecificPtr2() { return this; }

    // Constructor -- creates a new clause and add it to watcher lists.
    friend bool UpwardClause_new(Solver& S, Lit output_, const vec<Lit>& ps, UpwardClause*& out_clause);

    // Constraint interface:
    void remove    (Solver& S, bool just_dealloc = false) { }
    GClause propagate (Solver& S, Lit p, bool& keep_watch);
    void calcReason(Solver& S, Lit p, vec<Lit>& out_reason);
    void moveWatch(int i, Lit p);
};

#endif
