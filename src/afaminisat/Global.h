/************histOut**************************************************************************************
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

#ifndef Global_h
#define Global_h

#include <fstream>
#include <cassert>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <climits>
#include <cfloat>
#include <new>

//=================================================================================================
// Basic Types & Minor Things:

#ifdef _MSC_VER
typedef INT64              int64;
typedef UINT64             uint64;
typedef INT_PTR            intp;
typedef UINT_PTR           uintp;
#define I64_fmt "I64d"
#else
typedef long long          int64;
typedef unsigned long long uint64;
typedef __PTRDIFF_TYPE__   intp;
typedef unsigned __PTRDIFF_TYPE__ uintp;
#define I64_fmt "lld"
#endif

typedef const char  cchar;


// For derivation output (verbosity level 2)
#define L_LIT    "%sx%d"
#define L_lit(p) sign(p)?"~":"", var(p)


template<class T> static inline T min(T x, T y) { return (x < y) ? x : y; }
template<class T> static inline T max(T x, T y) { return (x > y) ? x : y; }

template <bool> struct STATIC_ASSERTION_FAILURE;
template <> struct STATIC_ASSERTION_FAILURE<true>{};
#define TEMPLATE_FAIL STATIC_ASSERTION_FAILURE<false>()


//=================================================================================================
// 'malloc()'-style memory allocation -- never returns NULL; aborts instead:


template<class T> static inline T* xmalloc(size_t size) {
    T*   tmp = (T*)malloc(size * sizeof(T));
    assert(size == 0 || tmp != NULL);
    return tmp; }

template<class T> static inline T* xrealloc(T* ptr, size_t size) {
    T*   tmp = (T*)realloc((void*)ptr, size * sizeof(T));
    assert(size == 0 || tmp != NULL);
    return tmp; }

template<class T> static inline void xfree(T *ptr) {
    if (ptr != NULL) free((void*)ptr); }


//=================================================================================================
// Random numbers:


// Returns a random float 0 <= x < 1. Seed must never be 0.
static inline double drand(double& seed) {
    seed *= 1389796;
    int q = (int)(seed / 2147483647);
    seed -= (double)q * 2147483647;
    return seed / 2147483647; }

// Returns a random integer 0 <= x < size. Seed must never be 0.
static inline int irand(double& seed, int size) {
    return (int)(drand(seed) * size); }


//=================================================================================================
// Time:


#ifdef _MSC_VER
#include <ctime>
static inline double cpuTime(void) {
    return (double)clock() / CLOCKS_PER_SEC; }
#else
#include <sys/time.h>
#include <sys/resource.h>
static inline double cpuTime(void) {
    struct rusage ru;
    getrusage(RUSAGE_SELF, &ru);
    return (double)ru.ru_utime.tv_sec + (double)ru.ru_utime.tv_usec / 1000000; }
#endif


//=================================================================================================
// 'vec' -- automatically resizable arrays (via 'push()' method):


// NOTE! Don't use this vector on datatypes that cannot be re-located in memory (with realloc)

template<class T>
class vec {
    T*  data;
    int cap;

    void     init(int size, const T& pad);

public:
    void     grow(int min_cap);

    int sz;

    // Types:
    typedef int Key;
    typedef T   Datum;

    // Constructors:
    vec(void)                   : data(NULL) , sz(0)   , cap(0)    { }
    vec(int size)               : data(NULL) , sz(0)   , cap(0)    { growTo(size); }
    vec(int size, const T& pad) : data(NULL) , sz(0)   , cap(0)    { growTo(size, pad); }
    vec(T* array, int size)     : data(array), sz(size), cap(size) { }      // (takes ownership of array -- will be deallocated with 'xfree()')
    vec(const vec<T>& v) : data(NULL), sz(0), cap(0) { v.copyTo(*this); }
    vec(vec<T>&& v) : data(v.data), sz(v.sz), cap(v.cap) { v.data = NULL; v.sz = 0; v.cap = 0; }
   ~vec(void)                                                      { clear(true); }

    vec<T>& operator=(vec<T> &&v) { 
      clear(true);
      data = v.data;
      sz = v.sz;
      cap = v.cap;
      v.data = NULL;
      v.sz = 0;
      v.cap = 0;
      return *this;
    }

    // Ownership of underlying array:
    T*       release  (void)           { T* ret = data; data = NULL; sz = 0; cap = 0; return ret; }
    operator T*       (void)           { return data; }     // (unsafe but convenient)
    operator const T* (void) const     { return data; }

    // Size operations:
    int      size   (void) const       { return sz; }
    void     shrink (int nelems)       { assert(nelems <= sz); for (int i = 0; i < nelems; i++) sz--, data[sz].~T(); }
    void     pop    (void)             { sz--, data[sz].~T(); }
    void     growTo (int size);
    void     growTo (int size, const T& pad);
    void     clear  (bool dealloc = false);

    // Stack interface:
    void     push  (void)              { if (sz == cap) grow(sz+1); new (&data[sz]) T()    ; sz++; }
    void     push  (const T& elem)     { if (sz == cap) grow(sz+1); new (&data[sz]) T(elem); sz++; }
    const T& last  (void) const        { return data[sz-1]; }
    T&       last  (void)              { return data[sz-1]; }

    template<class A>
    void     pushWithArg  (A a)     { if (sz == cap) grow(sz+1); new (&data[sz]) T(a); sz++; }

    // Vector interface:
    const T& operator [] (int index) const  { return data[index]; }
    T&       operator [] (int index)        { return data[index]; }

    // Don't allow copying (error prone):
    vec<T>&  operator = (vec<T>& other) { TEMPLATE_FAIL; }
             // vec        (vec<T>& other) { TEMPLATE_FAIL; }

    // Duplicatation (preferred instead):
    void copyTo(vec<T>& copy) const { copy.clear(); copy.growTo(sz); for (int i = 0; i < sz; i++) new (&copy[i]) T(data[i]); }
    void moveTo(vec<T>& dest) { dest.clear(true); dest.data = data; dest.sz = sz; dest.cap = cap; data = NULL; sz = 0; cap = 0; }
};

template<class T>
void vec<T>::grow(int min_cap) {
    if (min_cap <= cap) return;
    if (cap == 0) cap = (min_cap >= 2) ? min_cap : 2;
    else          do cap = (cap*3 + 1)>>1; while (cap < min_cap);
    data = xrealloc(data, cap); }

template<class T>
void vec<T>::growTo(int size, const T& pad) {
    if (sz >= size) return;
    grow(size);
    for (int i = sz; i < size; i++) new (&data[i]) T(pad);
    sz = size; }

template<class T>
void vec<T>::growTo(int size) {
    if (sz >= size) return;
    grow(size);
    for (int i = sz; i < size; i++) new (&data[i]) T();
    sz = size; }

template<class T>
void vec<T>::clear(bool dealloc) {
    if (data != NULL){
        for (int i = 0; i < sz; i++) data[i].~T();
        sz = 0;
        if (dealloc) xfree(data), data = NULL, cap = 0; } }


//=================================================================================================
// Lifted booleans:


class lbool {
    int     value;
    explicit lbool(int v) : value(v) { }

public:
    lbool()       : value(0) { }
    lbool(bool x) : value((int)x*2-1) { }
    int toInt(void) const { return value; }

    bool  operator == (const lbool& other) const { return value == other.value; }
    bool  operator != (const lbool& other) const { return value != other.value; }
    lbool operator ~  (void)               const { return lbool(-value); }

    friend int   toInt  (lbool l);
    friend lbool toLbool(int   v);
};
inline int   toInt  (lbool l) { return l.toInt(); }
inline lbool toLbool(int   v) { return lbool(v);  }

const lbool l_True  = toLbool( 1);
const lbool l_False = toLbool(-1);
const lbool l_Undef = toLbool( 0);

//=================================================================================================
// Relation operators -- extend definitions from '==' and '<'


#ifndef __SGI_STL_INTERNAL_RELOPS   // (be aware of SGI's STL implementation...)
#define __SGI_STL_INTERNAL_RELOPS
template <class T> static inline bool operator != (const T& x, const T& y) { return !(x == y); }
template <class T> static inline bool operator >  (const T& x, const T& y) { return y < x;     }
template <class T> static inline bool operator <= (const T& x, const T& y) { return !(y < x);  }
template <class T> static inline bool operator >= (const T& x, const T& y) { return !(x < y);  }
#endif

typedef int Var;
#define var_Undef (-1)


class Lit {
    int     x;
public:
    Lit(void)   /* unspecifed value allowed for efficiency */      { }
    explicit Lit(Var var, bool sign = false) : x((var+var) + sign) { }
    friend Lit operator ~ (Lit p) { Lit q; q.x = p.x ^ 1; return q; }

    friend bool sign (Lit p) { return p.x & 1; }
    friend int  var  (Lit p) { return p.x >> 1; }
    friend int  index(Lit p) { return p.x; }        // A "toInt" method that guarantees small, positive integers suitable for array indexing.
    friend Lit  toLit(int i);

    friend bool operator == (Lit p, Lit q) { return index(p) == index(q); }
    friend bool operator <  (Lit p, Lit q) { return index(p)  < index(q); }  // '<' guarantees that p, ~p are adjacent in the ordering.
};

inline Lit  toLit (int i) { Lit p; p.x = i; return p; }  // Inverse of 'index()'.

inline std::ostream& operator<<(std::ostream& os, Lit const &p) {
  return os << (sign(p) ? "~" : "") << "x" << var(p);
}

const Lit lit_Undef(var_Undef, false);  // }- Useful special constants.
const Lit lit_Error(var_Undef, true );  // }
const Lit lit_NoCandidate(-2, false);



inline void printClause(const vec<Lit> &c) {
    printf("{");
    for (int i = 0; i < c.size(); i++)
        printf(" " L_LIT, L_lit(c[i]));
    printf(" }");
}


#ifdef MY_DEBUG
extern int verbosity;
#else
int verbosity = -5;
#endif


//=================================================================================================
#endif
