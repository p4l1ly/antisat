#include <algorithm>

#include "SupQ.h"

using std::vector;

void SupQList::add(const vector<int> &clause) {
  sets.emplace_back();
  vector<int> &set = sets.back();
  set.reserve(clause.size());

  for (unsigned i = 0; i < clause.size(); ++i)
    set.push_back(clause[i]);
}

const vector<int>* SupQList::get(const vector<int> &clause) const {
  for (unsigned i = 0; i < sets.size(); i++) {
    if (std::includes(
          clause.begin(), clause.end(), sets[i].begin(), sets[i].end())
    ) {
      return &sets[i];
    }
  }

  return NULL;
}

const Reason SupQList::propagate(const vector<int> &clause) const {
  for (unsigned i = 0; i < sets.size(); i++) {
    unsigned a = 0, b = 0;
    int extra = -1;

    while (a < sets[i].size() && b < clause.size()) {
      if (clause[b] < sets[i][a]) b++;
      else if (sets[i][a] < clause[b]) {
        if (extra == -1) {
          extra = a;
          a++;
        }
        else goto outer_continue;
      }
      else {
        a++;
        b++;
      }
    }

    if (a < sets[i].size()) {
      if (a + 1 < sets[i].size() || extra != -1) continue;
      else extra = a;
    }

    if (extra == -1) return Reason{&sets[i], -2};  // the clause is a superset of a set
    else return Reason{&sets[i], sets[i][extra]};  // the clause propagates a literal from a set

outer_continue:
    continue;
  }

  return Reason{NULL, -1};  // we cannot propagate anything yet
}
