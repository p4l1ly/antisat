#include <algorithm>

#include "SupQ.h"

using std::vector;

bool SupQTrie::get_or_add(const vector<int> &clause) {
  if (Node::get(root, clause, 0)) return true;
  else {
    if (clause.size() == 0) root = NULL;
    else Node::add(root, clause);
    return false;
  }
}

bool Node::get(Node *node, const vector<int> &clause, unsigned ix) {
  if (node == NULL) return true;
  if (ix == clause.size()) return false;

  auto childs = node->childs;
  for (unsigned j = ix; j < clause.size(); j++) {
    auto it = childs.find(clause[j]);
    if (it == childs.end()) {
      return false;
    }

    if (get(it->second, clause, j + 1)) return true;
  }

  return false;
}

void Node::add(Node *node, const vector<int> &clause) {
  unsigned ix = 0;
  std::unordered_map<int, Node*>::iterator it;

  for (; ix < clause.size(); ++ix) {
    it = node->childs.find(clause[ix]);
    if (it != node->childs.end()) node = it->second;
    else break;
  }

  if (ix == clause.size()) it->second = NULL;
  else {
    while (true) {
      if (ix + 1 == clause.size()) {
        node->childs[clause[ix]] = NULL;
        break;
      }
      node = node->childs[clause[ix]] = new Node();
      ix++;
    }
  }
}
