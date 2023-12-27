#include <deque>
#include <set>
#include <vector>

using std::set;
using std::deque;
using std::vector;

#include "Global.h"

struct LeastSizeCompare
{
    bool operator()(const vector<int>* lhs, const vector<int>* rhs) const
    {
        if (lhs->size() != rhs->size()) return lhs->size() < rhs->size();

        // We're sure that the inserted elements are unequal and if the sizes are equal, we don't
        // care about the order.
        return true;

        // for (unsigned i = 0; i < lhs->size(); i++) {
        //     if ((*lhs)[i] != (*rhs)[i]) return (*lhs)[i] < (*rhs)[i];
        // }
        // return false;
    }
};


struct CellContainer {
    virtual void add(vector<int>* x) = 0;
    virtual int size() const = 0;
    virtual vector<int>* pop() = 0;
    virtual ~CellContainer() {};
};

class CellContainerSet : public CellContainer {
    set<vector<int>*, LeastSizeCompare> data;
public:
    CellContainerSet() {}
    void add(vector<int>* x) { data.insert(x); }
    int size() const { return data.size(); }
    vector<int>* pop() {
        auto it = data.begin();
        vector<int>* result = *it;
        data.erase(it);
        return result;
    }

    ~CellContainerSet() {
      for (vector<int> *x: data) {
        delete x;
      }
    }
};

class CellContainerBfs : public CellContainer {
    deque<vector<int>*> data;
public:
    CellContainerBfs() {}
    void add(vector<int>* x) { data.push_back(x); }
    int size() const { return data.size(); }
    vector<int>* pop() {
        vector<int>* result = data.front();
        data.pop_front();
        return result;
    }

    ~CellContainerBfs() {
      for (vector<int> *x: data) {
        delete x;
      }
    }
};

class CellContainerDfs : public CellContainer {
    vector<vector<int>*> data;
public:
    CellContainerDfs() {}
    void add(vector<int>* x) { data.push_back(x); }
    int size() const { return data.size(); }
    vector<int>* pop() {
        vector<int>* result = data.back();
        data.pop_back();
        return result;
    }

    ~CellContainerDfs() {
      for (vector<int> *x: data) {
        delete x;
      }
    }
};
