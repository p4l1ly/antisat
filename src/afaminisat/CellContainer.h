#include <deque>
#include <set>
#include <vector>

using std::set;
using std::deque;
using std::vector;

#include "Global.h"

struct LeastSizeCompare
{
    bool operator()(const vec<Lit>& lhs, const vec<Lit>& rhs) const
    {
        if (lhs.size() != rhs.size()) return lhs.size() < rhs.size();

        // We're sure that the inserted elements are unequal and if the sizes are equal, we don't
        // care about the order.
        return true;
    }
};


struct CellContainer {
    virtual void add(vec<Lit> &x) = 0;
    virtual int size() const = 0;
    virtual vec<Lit> pop() = 0;
    virtual ~CellContainer() {};
};

class CellContainerSet : public CellContainer {
    set<vec<Lit>, LeastSizeCompare> data;
public:
    CellContainerSet() {}
    void add(vec<Lit> &x) { data.emplace(std::move(x)); }
    int size() const { return data.size(); }
    vec<Lit> pop() {
        auto it = data.begin();
        vec<Lit> result(std::move(*it));
        data.erase(it);
        return std::move(result);
    }
};

class CellContainerBfs : public CellContainer {
    deque<vec<Lit>> data;
public:
    CellContainerBfs() {}
    void add(vec<Lit>& x) { data.emplace_back(std::move(x)); }
    int size() const { return data.size(); }
    vec<Lit> pop() {
      vec<Lit> result(std::move(data.front()));
      data.pop_front();
      return std::move(result);
    }
};

class CellContainerDfs : public CellContainer {
    vector<vec<Lit>> data;
public:
    CellContainerDfs() {}
    void add(vec<Lit>& x) { data.emplace_back(std::move(x)); }
    int size() const { return data.size(); }
    vec<Lit> pop() {
      vec<Lit> result(std::move(data.back()));
      data.pop_back();
      return std::move(result);
    }
};
