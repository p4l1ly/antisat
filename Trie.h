#ifndef Trie_h
#define Trie_h

#include <vector>
#include <iostream>
#include <unordered_set>

using std::cout;
using std::vector;
using std::unordered_set;

//=================================================================================================

struct VerStart;

struct Hor {
  unsigned parent_hor_ix;
  int parent_ver_ix;
  Hor *parent;
  vector<struct VerStart> vers;

  Hor(unsigned parent_hor_ix_, int parent_ver_ix_, Hor *parent)
  : parent_hor_ix(parent_hor_ix_)
  , parent_ver_ix(parent_ver_ix_)
  , parent(parent)
  , vers()
  {}
};

struct HorStart {
  int tag;
  Hor hor;

  HorStart(
    int tag_,
    unsigned parent_hor_ix,
    unsigned parent_ver_ix,
    Hor *parent
  )
  : tag(tag_), hor(parent_hor_ix, parent_ver_ix, parent)
  {}
};

struct VerStart {
  int tag;
  vector<HorStart> hors;

  VerStart(unsigned parent_hor_ix, Hor *parent, unordered_set<int> xs)
  : hors()
  {
    auto iter = xs.begin();
    tag = *iter;
    xs.erase(iter);

    hors.reserve(xs.size());

    int i = 0;
    for (int x: xs) {
      hors.emplace_back(x, parent_hor_ix, i, parent);
      i++;
    }
  }
};

class Trie {
public:
  Hor root;
  Hor *active_hor;
  unsigned int hor_ix = 0;
  int ver_ix = -1;

  Trie() : root(0, -1, NULL) {
    active_hor = &root;
  }

  int guess() {
    if (ver_ix >= 0) {
      return active_hor->vers[hor_ix].hors[ver_ix].tag;
    }
    else if (hor_ix < active_hor->vers.size()) {
      cout << "guess\n";
      return active_hor->vers[hor_ix].tag;
    }
    else {
      return -1;
    }
  }

  void add(vector<int> xs) {
    unordered_set<int> xs_set(xs.begin(), xs.end());
    Hor *hor_iter = active_hor;

    while (hor_iter->parent) {
      for (int i = hor_iter->parent_ver_ix - 1; i >= 0; --i) {
        xs_set.erase(
          hor_iter->parent->vers[hor_iter->parent_hor_ix].hors[i].tag);
      }
      xs_set.erase(hor_iter->parent->vers[hor_iter->parent_hor_ix].tag);
      hor_iter = hor_iter->parent;
    }

    active_hor->vers.emplace_back(active_hor->vers.size(), active_hor, xs_set);
    cout << active_hor->vers.size() << "add\n";
  }
};

//=================================================================================================
#endif
