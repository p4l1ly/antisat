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

#ifndef SubQ_h
#define SubQ_h

#include "Global.h"
#include <vector>
#include <algorithm>
#include <chrono>

using std::vector;
namespace chrono = std::chrono;

//=================================================================================================

struct SupQ {
public:
  chrono::duration<double> elapsed_add;
  chrono::duration<double> elapsed_get;

  SupQ()
  : elapsed_add(chrono::duration<double>::zero())
  , elapsed_get(chrono::duration<double>::zero())
  {}

  virtual void add(const vec<Lit> &clause) {}
  virtual bool get(const vec<Lit> &clause) { return false; }

  virtual ~SupQ() {}
};

class SupQVec : public SupQ {
  vector<vector<int>> sets;
public:
  void add(const vec<Lit> &clause) {
    auto tic = chrono::steady_clock::now();

    sets.emplace_back();
    vector<int> &set = sets.back();
    set.reserve(clause.size());

    for (int i = 0; i < clause.size(); ++i)
      set.push_back(var(clause[i]));

    elapsed_add = elapsed_add + chrono::steady_clock::now() - tic;
  }

  bool get(const vec<Lit> &clause) {
    auto tic = chrono::steady_clock::now();

    vector<int> set;
    set.reserve(clause.size());
    for (int i = 0; i < clause.size(); ++i)
      set.push_back(var(clause[i]));

    for (unsigned i = 0; i < sets.size(); i++) {
      if (std::includes(
            set.begin(), set.end(), sets[i].begin(), sets[i].end())
      ) {
        elapsed_get = elapsed_get + chrono::steady_clock::now() - tic;
        return true;
      }
    }

    elapsed_get = elapsed_get + chrono::steady_clock::now() - tic;
    return false;
  }

};

//=================================================================================================
#endif

