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

#include "Constraints.h"
#include "Solver.h"
#include "Sort.h"
#include "Global.h"

#include <iostream>
#include <cstdlib>

using std::swap;

//=================================================================================================
// Helpers:


void removeWatch(vec<Constr*>& ws, Constr* elem)
{
    int j = 0;
    for (; ws[j] != elem  ; j++) assert(j < ws.size());
    for (; j < ws.size()-1; j++) ws[j] = ws[j+1];
    ws.pop();
}


//=================================================================================================
// Clause constraint:


// Returns FALSE if top-level conflict detected (must be handled); TRUE otherwise.
// 'out_clause' may be set to NULL if clause is already satisfied by the top-level assignment.
//
bool Clause_new(Solver& S, const vec<Lit>& ps_, bool learnt, Clause*& out_clause)
{
    vec<Lit>    qs;
    out_clause = NULL;

    if (!learnt){
        assert(S.decisionLevel() == 0);
        ps_.copyTo(qs);             // Make a copy of the input vector.

        // Remove false literals:
        for (int i = 0; i < qs.size();){
            if (S.value(qs[i]) != l_Undef){
                if (S.value(qs[i]) == l_True)
                    return true;    // Clause always true -- don't add anything.
                else
                    qs[i] = qs.last(),
                    qs.pop();
            }else
                i++;
        }

        // Remove duplicates:
        sortUnique(qs);
        for (int i = 0; i < qs.size()-1; i++){
            if (qs[i] == ~qs[i+1])
                return true;        // Clause always true -- don't add anything.
        }
    }
    const vec<Lit>& ps = learnt ? ps_ : qs;     // 'ps' is now the (possibly) reduced vector of literals.

    if (ps.size() == 0)
        return false;
    else if (ps.size() == 1)
        return S.enqueue(ps[0]);
    else{
        // Allocate clause:
        assert(sizeof(Lit)   == sizeof(unsigned));
        assert(sizeof(float) == sizeof(unsigned));
        void*   mem = xmalloc<char>(sizeof(Clause) + sizeof(unsigned)*(ps.size() + (int)learnt));
        Clause* c   = new (mem) Clause;

        c->size_learnt = (int)learnt | (ps.size() << 1);
        for (int i = 0; i < ps.size(); i++) c->data[i] = ps[i];

        // For learnt clauses only:
        if (learnt){
            c->activity() = 0.0;

            // Put the second watch on the literal with highest decision level:
            int     max_i = 1;
            int     max   = S.level[var(ps[1])];
            for (int i = 2; i < ps.size(); i++)
                if (S.level[var(ps[i])] > max)
                    max   = S.level[var(ps[i])],
                    max_i = i;
            c->data[1]     = ps[max_i];
            c->data[max_i] = ps[1];

            // Bumping:
            S.claBumpActivity(c); // (newly learnt clauses should be considered active)

            S.stats.learnts++;
            S.stats.learnts_literals += c->size();
        }else{
            S.stats.clauses++;
            S.stats.clauses_literals += c->size();
        }

        // Store clause:
        S.watches[index(~c->data[0])].push(c);
        S.watches[index(~c->data[1])].push(c);
        out_clause = c;

        return true;
    }
}

bool Clause_new_handleConflict(Solver& S, vec<Lit>& ps, Clause*& out_clause)
{
    out_clause = NULL;
    sortUnique(ps);

    if (ps.size() == 1) ps.push(Lit(ps[0]));

    // Allocate clause:
    assert(sizeof(Lit)   == sizeof(unsigned));
    assert(sizeof(float) == sizeof(unsigned));
    void* mem = xmalloc<char>(sizeof(Clause) + sizeof(unsigned)*ps.size());
    Clause* c   = new (mem) Clause;

    c->size_learnt = ps.size() << 1;
    for (int i = 0; i < ps.size(); i++) c->data[i] = ps[i];

    S.stats.clauses++;
    S.stats.clauses_literals += c->size();

    int max_level = S.level[var(c->data[0])];
    int max_level2 = S.level[var(c->data[1])];

    if (max_level < max_level2) {
      swap(max_level, max_level2);
      swap(c->data[0], c->data[1]);
    }

    // make the first two literals have the highest levels of all literals
    int level;
    for (int i = 2; i < ps.size(); i++) {
      level = S.level[var(c->data[i])];
      if (level > max_level) {
        max_level2 = max_level;
        max_level = level;
        swap(c->data[0], c->data[1]);
        swap(c->data[0], c->data[i]);
      }
      else if (level > max_level2) {
        max_level2 = level;
        swap(c->data[1], c->data[i]);
      }
    }

    // add watches
    S.watches[index(~c->data[0])].push(c);
    S.watches[index(~c->data[1])].push(c);
    out_clause = c;
    return false;
}

int  Clause::max_level(const Solver& S) const { return S.level[var(data[0])]; }


bool Clause::locked(const Solver& S) const {
    return (const Clause *)S.reason[var(data[0])] == this; }


void Clause::remove(Solver& S, bool just_dealloc)
{
    if (!just_dealloc){
        removeWatch(S.watches[index(~data[0])], this);
        removeWatch(S.watches[index(~data[1])], this); }

    if (learnt()){
        S.stats.learnts--;
        S.stats.learnts_literals -= size();
    }else{
        S.stats.clauses--;
        S.stats.clauses_literals -= size();
    }

    xfree(this);
}


// Can assume everything has been propagated! (esp. the first two literals are != l_False, unless
// the clause is binary and satisfied, in which case the first literal is true)
// Returns True if clause is satisfied (will be removed), False otherwise.
//
bool Clause::simplify(Solver& S)
{
    assert(S.decisionLevel() == 0);
    for (int i = 0; i < size(); i++){
        if (S.value(data[i]) == l_True)
            return true;
    }
    return false;
}


// 'p' is the literal that became TRUE
bool Clause::propagate(Solver& S, Lit p, bool& keep_watch)
{
    // Make sure the false literal is data[1]:
    Lit     false_lit = ~p;
    if (data[0] == false_lit)
        data[0] = data[1], data[1] = false_lit;
    assert(data[1] == false_lit);

    // If 0th watch is true, then clause is already satisfied.
    if (S.value(data[0]) == l_True){
        keep_watch = true;
        return true; }

    // Look for new watch:
    for (int i = 2; i < size(); i++){
        if (S.value(data[i]) != l_False){
            data[1] = data[i], data[i] = false_lit;
            S.watches[index(~data[1])].push(this);
            return true; } }

    // Clause is unit under assignment:
    keep_watch = true;
    return S.enqueue(data[0], this);
}


// Can assume 'out_reason' to be empty.
// Calculate reason for 'p'. If 'p == lit_Undef', calculate reason for conflict.
//
void Clause::calcReason(Solver& S, Lit p, vec<Lit>& out_reason)
{
    assert(p == lit_Undef || p == data[0]);

    for (int i = ((p == lit_Undef) ? 0 : 1); i < size(); i++) {
        assert(S.value(data[i]) == l_False);
        out_reason.push(~data[i]);
    }
    if (learnt()) S.claBumpActivity(this);
}


//=================================================================================================
// AtMost constraint -- An example of extending MiniSat:


// Pre-condition: All variables must be distinct and unbound. (To lift this pre-condition,
// any fact immediately derivable from the new constraint should be enqueued by 'enqueue()'.
// If the constraint is already satisfied under the current top-level assignment, it should
// not be constructed at all.)
//
bool AtMost_new(Solver& S, const vec<Lit>& ps, int n, AtMost*& out)
{
    assert(S.decisionLevel() == 0);

    void* mem    = (void*)xmalloc<char>(sizeof(AtMost) + sizeof(Lit) * ps.size());
    out          = new (mem) AtMost;
    out->size    = ps.size();
    out->n       = n;
    out->counter = 0;
    for (int i = 0; i < ps.size(); i++) out->lits[i] = ps[i];
    for (int i = 0; i < ps.size(); i++) S.watches[index(ps[i])].push(out);

    return true;
}


void AtMost::remove(Solver& S, bool just_dealloc) {
    if (!just_dealloc)
        for (int i = 0; i < size; i++)
            removeWatch(S.watches[index(lits[i])], this);
    xfree(this);
}


bool AtMost::simplify(Solver& S) {
    return false; }


bool AtMost::propagate(Solver& S, Lit p, bool& keep_watch)
{
    keep_watch = true;
    if (counter == n) return false;

    counter++;
    S.undos[var(p)].push(this);

    // If no more can be true, enqueue the negation of the rest:
    if (counter == n)
        for (int i = 0; i < size; i++)
            if (!S.enqueue(~lits[i], this))
                return false;
    return true;
}


void AtMost::undo(Solver& S, Lit p) {
    counter--; }


void AtMost::calcReason(Solver& S, Lit p, vec<Lit>& out_reason)
{
    int     c = (p == lit_Undef) ? -1 : 0;
    for (int i = 0; i < size; i++){
        if (S.value(lits[i]) == l_True){
            out_reason.push(lits[i]);
            if (++c == n) return;
        }
    }
}
