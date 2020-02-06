#ifndef SupQ_h
#define SupQ_h

#include <vector>
#include <algorithm>
#include <chrono>

using std::vector;
namespace chrono = std::chrono;

//=================================================================================================

typedef struct ReasonStruct {
  const vector<int>* clause;
  int index;
} Reason;

struct SupQList {
public:
  vector<vector<int>> sets;

  SupQList() {}
  void add(const vector<int> &clause);
  const vector<int>* get(const vector<int> &clause) const;
  const Reason propagate(const vector<int> &clause) const;
  ~SupQList() {}
};

struct MeasuredSupQ {
public:
  chrono::duration<double> elapsed_add;
  chrono::duration<double> elapsed_get;
  SupQList supq;

  MeasuredSupQ()
  : elapsed_add(chrono::duration<double>::zero())
  , elapsed_get(chrono::duration<double>::zero())
  {}

  void add(const vector<int> &clause) {
    auto tic = chrono::steady_clock::now();
    supq.add(clause);
    elapsed_add = elapsed_add + chrono::steady_clock::now() - tic;
  }

  const vector<int>* get(const vector<int> &clause) {
    auto tic = chrono::steady_clock::now();
    const vector<int>* result = supq.get(clause);
    elapsed_get = elapsed_get + chrono::steady_clock::now() - tic;
    return result;
  }

  const Reason propagate(const vector<int> &clause) {
    auto tic = chrono::steady_clock::now();
    const Reason result = supq.propagate(clause);
    elapsed_get = elapsed_get + chrono::steady_clock::now() - tic;
    return result;
  }

  virtual ~MeasuredSupQ() {}
};

//=================================================================================================
#endif
