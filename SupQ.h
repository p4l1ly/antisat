#ifndef SupQ_h
#define SupQ_h

#include <vector>
#include <unordered_map>
#include <algorithm>
#include <chrono>

using std::vector;
namespace chrono = std::chrono;

//=================================================================================================
struct Node {
  std::unordered_map<int, Node*> childs;

  Node() : childs() {}

  static bool get(Node *node, const vector<int> &clause, unsigned ix);
  static void add(Node *node, const vector<int> &clause);

  ~Node() {
    for (auto keyval: childs) {
      if (keyval.second != NULL)
        delete keyval.second;
    }
  }
};

struct SupQTrie {
public:
  Node *root;

  SupQTrie() : root(new Node()) {}
  bool get_or_add(const vector<int> &clause);
  ~SupQTrie() {
    if (root != NULL) delete root;
  }
};

struct MeasuredSupQ {
public:
  chrono::duration<double> elapsed_add;
  chrono::duration<double> elapsed_get;
  SupQTrie supq;

  MeasuredSupQ()
  : elapsed_add(chrono::duration<double>::zero())
  , elapsed_get(chrono::duration<double>::zero())
  {}

  bool get_or_add(const vector<int> &clause) {
    auto tic = chrono::steady_clock::now();
    bool result = supq.get_or_add(clause);
    elapsed_get = elapsed_get + chrono::steady_clock::now() - tic;
    return result;
  }

  virtual ~MeasuredSupQ() {}
};

//=================================================================================================
#endif
