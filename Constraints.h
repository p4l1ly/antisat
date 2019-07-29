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

#include "SolverTypes.h"


//=================================================================================================
// Constraint abstraction:


class Solver;

struct Constr {
    virtual void remove    (Solver& S, bool just_dealloc = false) = 0;
    virtual bool propagate (Solver& S, Lit p, bool& keep_watch) = 0;    // ('keep_watch' is set to FALSE beftore call to this method)
    virtual bool simplify  (Solver& S) { return false; };
    virtual void undo      (Solver& S, Lit p) { };
    virtual void calcReason(Solver& S, Lit p, vec<Lit>& out_reason) = 0;

    virtual ~Constr(void) { };  // (not used, just to keep the compiler happy)
};


//=================================================================================================
// Clauses:


class Clause : public Constr {
    unsigned    size_learnt;
    Lit         data[0];

public:
    int  max_level   (const Solver& S) const;
    int  size        (void)      const { return size_learnt >> 1; }
    bool learnt      (void)      const { return size_learnt & 1; }
    Lit  operator [] (int index) const { return data[index]; }

    // Constructor -- creates a new clause and add it to watcher lists.
    friend bool Clause_new(Solver& S, const vec<Lit>& ps, bool learnt, Clause*& out_clause);
    friend bool Clause_new_handleConflict(Solver& S, vec<Lit>& ps, Clause*& out_clause);

    // Learnt clauses only:
    bool    locked  (const Solver& S) const;
    float&  activity(void) const { return *((float*)&data[size()]); }

    // Constraint interface:
    void remove    (Solver& S, bool just_dealloc = false);
    bool propagate (Solver& S, Lit p, bool& keep_watch);
    bool simplify  (Solver& S);
    void calcReason(Solver& S, Lit p, vec<Lit>& out_reason);
};


//=================================================================================================
// AtMost:


class AtMost : public Constr {
    int     n;
    int     counter;
    int     size;
    Lit     lits[0];

public:
    // Constructor -- creates a new AtMost-constraint and add it to watcher lists.
    friend bool AtMost_new(Solver& S, const vec<Lit>& ps, int n, AtMost*& out);

    // Constraint interface:
    void remove    (Solver& S, bool just_dealloc = false);
    bool propagate (Solver& S, Lit p, bool& keep_watch);
    bool simplify  (Solver& S);
    void undo      (Solver& S, Lit p);
    void calcReason(Solver& S, Lit p, vec<Lit>& out_reason);
};


/*
//=================================================================================================
// AtLeast:


class AtLeast : public Constr {
    int     n;
    int     counter;
    int     size;
    Lit     lits[0];

public:
    // Constructor -- creates a new AtMost-constraint and add it to watcher lists.
    friend bool AtLeast_new(Solver& S, const vec<Lit>& ps, int n, AtLeast*& out);

    // Constraint interface:
    void remove    (Solver& S, bool just_dealloc = false);
    bool propagate (Solver& S, Lit p, bool& keep_watch);
    bool simplify  (Solver& S);
    void undo      (Solver& S, Lit p);
    void calcReason(Solver& S, Lit p, vec<Lit>& out_reason);
};
//=================================================================================================
*/

#endif
