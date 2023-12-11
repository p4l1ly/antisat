#include "Solver.h"

#ifdef MY_DEBUG
int verbosity = 4;
#endif


lbool init_test(
  Solver &S,
  int nVars,
  const std::unordered_set<unsigned> finals = std::unordered_set<unsigned>()
) {
  S.pures.growTo(nVars, false);
  S.output_map.growTo(nVars, -1);

  for (int i = 0; i < nVars; ++i) S.newVar();

  vec<Lit> trie_lits;

  for (int i = 0; i < nVars; ++i) trie_lits.push(Lit(i));

  if (!S.trie.init(trie_lits, finals)) return l_True;
  S.root_level = 0;
  if (S.trie.reset(S)) return l_False;
  return l_Undef;
}


void test_init_twolit() {
  Solver S;
  assert(init_test(S, 2) == l_Undef);
  assert(S.value(Lit(0)) == l_Undef);
  assert(S.value(Lit(1)) == l_Undef);

  assert(S.trie.accepting_place.hor == NULL);
}


void test_init_onelit() {
  Solver S;
  assert(init_test(S, 1) == l_Undef);
  assert(S.value(Lit(0)) == l_True);
  S.propagate();

  assert(S.trie.accepting_place.hor == &S.trie.root);
  assert(S.trie.accepting_place.hor_ix == 0);
  assert(S.trie.accepting_place.ver_ix == IX_NULL);
  assert(S.trie.accepting_rear_visit_level == 0);
  assert(S.trie.accepting_van_visit_level == 0);
  assert(S.trie.accepting_reusable_van == &S.trie.root_new_vans[0]);
  assert(S.trie.accepting_reusable_rear == &S.trie.root_new_rears[0]);
}


void test_twolit_conflict() {
  Solver S;
  assert(init_test(S, 2) == l_Undef);
  assert(S.value(Lit(0)) == l_Undef);
  assert(S.value(Lit(1)) == l_Undef);

  S.enqueue(~Lit(0));
  S.enqueue(~Lit(1));

  Reason *conflict_reason = S.propagate();
  assert(conflict_reason != NULL);
  assert(S.value(Lit(0)) == l_False);
  assert(S.value(Lit(1)) == l_False);

  assert(S.watches[index(Lit(0))].size() == 0);
  assert(S.watches[index(~Lit(0))].size() == 0);
  assert(S.watches[index(Lit(1))].size() == 0);
  assert(S.watches[index(~Lit(1))].size() == 0);

  assert(S.trie.accepting_place.hor == NULL);
}


void test_twolit_jump() {
  Solver S;
  assert(init_test(S, 2) == l_Undef);
  assert(S.value(Lit(0)) == l_Undef);
  assert(S.value(Lit(1)) == l_Undef);

  S.enqueue(~Lit(0));
  assert(S.propagate() == NULL);
  assert(S.value(Lit(0)) == l_False);
  assert(S.value(Lit(1)) == l_True);

  assert(S.trie.accepting_place.hor == &S.trie.root);
  assert(S.trie.accepting_place.hor_ix == 0);
  assert(S.trie.accepting_place.ver_ix == 0);
  assert(S.trie.accepting_rear_visit_level == 0);
  assert(S.trie.accepting_van_visit_level == 0);
  assert(S.trie.accepting_reusable_van == &S.trie.root_new_vans[0]);
  assert(S.trie.accepting_reusable_rear == &S.trie.root_new_rears[0]);
}

void test_twolit_van_accept() {
  Solver S;
  assert(init_test(S, 2) == l_Undef);
  assert(S.value(Lit(0)) == l_Undef);
  assert(S.value(Lit(1)) == l_Undef);

  S.enqueue(Lit(1));
  assert(S.propagate() == NULL);
  assert(S.value(Lit(0)) == l_Undef);
  assert(S.value(Lit(1)) == l_True);

  S.enqueue(~Lit(0));
  assert(S.propagate() == NULL);
  assert(S.value(Lit(0)) == l_False);
  assert(S.value(Lit(1)) == l_True);

  assert(S.trie.accepting_place.hor == &S.trie.root);
  assert(S.trie.accepting_place.hor_ix == 0);
  assert(S.trie.accepting_place.ver_ix == 0);
  assert(S.trie.accepting_rear_visit_level == 0);
  assert(S.trie.accepting_van_visit_level == 0);
  assert(S.trie.accepting_reusable_van == &S.trie.root_new_vans[0]);
  assert(S.trie.accepting_reusable_rear == &S.trie.root_new_rears[0]);
}

void test_twolit_van_exhaust() {
  Solver S;
  assert(init_test(S, 2) == l_Undef);
  assert(S.value(Lit(0)) == l_Undef);
  assert(S.value(Lit(1)) == l_Undef);

  S.enqueue(~Lit(1));
  assert(S.propagate() == NULL);
  assert(S.value(Lit(0)) == l_True);
  assert(S.value(Lit(1)) == l_False);

  assert(S.trie.accepting_place.hor == &S.trie.root);
  assert(S.trie.accepting_place.hor_ix == 0);
  assert(S.trie.accepting_place.ver_ix == IX_NULL);
  assert(S.trie.accepting_rear_visit_level == 0);
  assert(S.trie.accepting_van_visit_level == 0);
  assert(S.trie.accepting_reusable_van == &S.trie.root_new_vans[0]);
  assert(S.trie.accepting_reusable_rear == &S.trie.root_new_rears[0]);
}

void test_twolit_rear_accept_then_van_accept() {
  Solver S;
  assert(init_test(S, 2) == l_Undef);
  assert(S.value(Lit(0)) == l_Undef);
  assert(S.value(Lit(1)) == l_Undef);

  S.enqueue(Lit(0));
  assert(S.propagate() == NULL);
  assert(S.value(Lit(0)) == l_True);
  assert(S.value(Lit(1)) == l_Undef);

  S.enqueue(Lit(1));
  assert(S.propagate() == NULL);
  assert(S.value(Lit(0)) == l_True);
  assert(S.value(Lit(1)) == l_True);

  assert(S.trie.accepting_place.hor == &S.trie.root);
  assert(S.trie.accepting_place.hor_ix == 0);
  assert(S.trie.accepting_place.ver_ix == IX_NULL);
  assert(S.trie.accepting_rear_visit_level == 0);
  assert(S.trie.accepting_van_visit_level == 0);
  assert(S.trie.accepting_reusable_van == &S.trie.root_new_vans[0]);
  assert(S.trie.accepting_reusable_rear == &S.trie.root_new_rears[0]);
}

void test_twolit_rear_accept_then_van_exhaust() {
  Solver S;
  assert(init_test(S, 2) == l_Undef);
  assert(S.value(Lit(0)) == l_Undef);
  assert(S.value(Lit(1)) == l_Undef);

  S.enqueue(Lit(0));
  assert(S.propagate() == NULL);
  assert(S.value(Lit(0)) == l_True);
  assert(S.value(Lit(1)) == l_Undef);

  S.enqueue(~Lit(1));
  assert(S.propagate() == NULL);
  assert(S.value(Lit(0)) == l_True);
  assert(S.value(Lit(1)) == l_False);

  assert(S.trie.accepting_place.hor == &S.trie.root);
  assert(S.trie.accepting_place.hor_ix == 0);
  assert(S.trie.accepting_place.ver_ix == IX_NULL);
  assert(S.trie.accepting_rear_visit_level == 0);
  assert(S.trie.accepting_van_visit_level == 0);
  assert(S.trie.accepting_reusable_van == &S.trie.root_new_vans[0]);
  assert(S.trie.accepting_reusable_rear == &S.trie.root_new_rears[0]);
}

void test_L() {
  Solver S;
  std::unordered_set<unsigned> finals({2});
  assert(init_test(S, 3, finals) == l_Undef);
  assert(S.value(Lit(0)) == l_Undef);
  assert(S.value(Lit(1)) == l_Undef);
  assert(S.value(Lit(2)) == l_Undef);

  S.trie.root.elems[0].hors[0].hor = new HorLine{Place{&S.trie.root, 0, 0}};
  S.trie.root.elems[0].hors[0].hor->elems.emplace_back(Lit(2));

  /////////////////////////////////////////////////////////////////////////////////////////////////
  // Reset, then propagate ~Lit(0).

  assert(S.trie.reset(S) == NULL);

  assert(S.value(Lit(0)) == l_Undef);
  assert(S.value(Lit(1)) == l_Undef);
  assert(S.value(Lit(2)) == l_Undef);

  S.enqueue(~Lit(0));
  assert(S.propagate() == NULL);
  assert(S.value(Lit(0)) == l_False);
  assert(S.value(Lit(1)) == l_True);
  assert(S.value(Lit(2)) == l_True);

  assert(S.trie.accepting_place.hor == S.trie.root.elems[0].hors[0].hor);
  assert(S.trie.accepting_place.hor_ix == 0);
  assert(S.trie.accepting_place.ver_ix == IX_NULL);
  assert(S.trie.accepting_rear_visit_level == 0);
  assert(S.trie.accepting_van_visit_level == 0);
  assert(S.trie.accepting_reusable_van == &S.trie.root_new_vans[1]);
  assert(S.trie.accepting_reusable_rear == &S.trie.root_new_rears[1]);

  /////////////////////////////////////////////////////////////////////////////////////////////////
  // Set ~Lit(0) before reset.

  assert(S.undos.size() == 0);
  for (int i = 0; i < 3; ++i) S.undoOne();
  S.enqueue(~Lit(0));
  S.propQ.clear();

  assert(S.value(Lit(0)) == l_False);
  assert(S.value(Lit(1)) == l_Undef);
  assert(S.value(Lit(2)) == l_Undef);

  assert(S.trie.reset(S) == NULL);
  assert(S.value(Lit(0)) == l_False);
  assert(S.value(Lit(1)) == l_True);
  assert(S.value(Lit(2)) == l_True);
  assert(S.propagate() == NULL);

  assert(S.watches[index(Lit(0))].size() == 0);
  assert(S.watches[index(~Lit(0))].size() == 0);
  assert(S.watches[index(Lit(1))].size() == 0);
  assert(S.watches[index(~Lit(1))].size() == 0);
  assert(S.watches[index(Lit(2))].size() == 0);
  assert(S.watches[index(~Lit(2))].size() == 0);

  assert(S.trie.accepting_place.hor == S.trie.root.elems[0].hors[0].hor);
  assert(S.trie.accepting_place.hor_ix == 0);
  assert(S.trie.accepting_place.ver_ix == IX_NULL);
  assert(S.trie.accepting_rear_visit_level == 0);
  assert(S.trie.accepting_van_visit_level == 0);
  assert(S.trie.accepting_reusable_van == &S.trie.root_new_vans[1]);
  assert(S.trie.accepting_reusable_rear == &S.trie.root_new_rears[1]);

  /////////////////////////////////////////////////////////////////////////////////////////////////
  // ~Lit(2) forces Lit(0), the rear guard then accepts.

  assert(S.undos.size() == 0);
  for (int i = 0; i < 3; ++i) S.undoOne();
  S.enqueue(~Lit(2));
  S.propQ.clear();

  assert(S.trie.reset(S) == NULL);
  assert(S.value(Lit(0)) == l_True);
  assert(S.value(Lit(1)) == l_Undef);
  assert(S.value(Lit(2)) == l_False);
  S.propagate();

  assert(S.trie.accepting_place.hor == &S.trie.root);
  assert(S.trie.accepting_place.hor_ix == 0);
  assert(S.trie.accepting_place.ver_ix == IX_NULL);
  assert(S.trie.accepting_rear_visit_level == 0);
  assert(S.trie.accepting_van_visit_level == 0);
  assert(S.trie.accepting_reusable_van == &S.trie.root_new_vans[0]);
  assert(S.trie.accepting_reusable_rear == &S.trie.root_new_rears[0]);

  /////////////////////////////////////////////////////////////////////////////////////////////////

  assert(S.watches[index(Lit(1))].size() == 1);
  assert(S.watches[index(~Lit(1))].size() == 1);
  assert(((VanGuard *)S.watches[index(Lit(1))][0])->enabled);
  ((VanGuard *)S.watches[index(Lit(1))][0])->enabled = false;
  S.watches[index(Lit(1))].clear();
  S.watches[index(~Lit(1))].clear();

  assert(S.undos.size() == 0);
  for (int i = 0; i < 2; ++i) S.undoOne();
  S.enqueue(~Lit(0));
  S.enqueue(~Lit(2));
  S.propQ.clear();

  Reason *conflict_reason = S.trie.reset(S);
  assert(conflict_reason != NULL);
  vec<Lit> out_reason;
  conflict_reason->calcReason(S, lit_Undef, out_reason);

  std::unordered_set<int> out_reason_set;
  for (int i = 0; i < out_reason.size(); i++) out_reason_set.insert(index(out_reason[i]));
  assert(out_reason_set == std::unordered_set({index(~Lit(0)), index(~Lit(2))}));

  assert(S.trie.accepting_place.hor == NULL);

  /////////////////////////////////////////////////////////////////////////////////////////////////

  assert(S.watches[index(Lit(1))].size() == 1);
  assert(S.watches[index(~Lit(1))].size() == 1);
  assert(((VanGuard *)S.watches[index(Lit(1))][0])->enabled);
  ((VanGuard *)S.watches[index(Lit(1))][0])->enabled = false;
  S.watches[index(Lit(1))].clear();
  S.watches[index(~Lit(1))].clear();

  assert(S.undos.size() == 0);
  for (int i = 0; i < 2; ++i) S.undoOne();
  S.enqueue(~Lit(0));
  S.enqueue(~Lit(1));
  S.propQ.clear();

  {
    Reason *conflict_reason = S.trie.reset(S);
    assert(conflict_reason != NULL);
    vec<Lit> out_reason;
    conflict_reason->calcReason(S, lit_Undef, out_reason);

    std::unordered_set<int> out_reason_set;
    for (int i = 0; i < out_reason.size(); i++) out_reason_set.insert(index(out_reason[i]));
    assert(out_reason_set == std::unordered_set({index(~Lit(0)), index(~Lit(1))}));

    assert(S.watches[index(Lit(2))].size() == 0);
    assert(S.watches[index(~Lit(2))].size() == 0);

    assert(S.trie.accepting_place.hor == NULL);
  }
}


void test_cap() {
  Solver S;
  std::unordered_set<unsigned> finals({2, 3});
  assert(init_test(S, 4, finals) == l_Undef);
  assert(S.value(Lit(0)) == l_Undef);
  assert(S.value(Lit(1)) == l_Undef);
  assert(S.value(Lit(2)) == l_Undef);
  assert(S.value(Lit(3)) == l_Undef);

  S.trie.root.elems.emplace_back(Lit(2));
  S.trie.root.elems[1].hors.emplace_back(Lit(3), 1);
  assert(S.trie.reset(S) == NULL);

  S.enqueue(~Lit(3));
  assert(S.propagate() == NULL);

  assert(S.value(Lit(0)) == l_Undef);
  assert(S.value(Lit(1)) == l_Undef);
  assert(S.value(Lit(2)) == l_True);
  assert(S.value(Lit(3)) == l_False);

  S.enqueue(~Lit(0));
  assert(S.propagate() == NULL);

  assert(S.value(Lit(0)) == l_False);
  assert(S.value(Lit(1)) == l_True);
  assert(S.value(Lit(2)) == l_True);
  assert(S.value(Lit(3)) == l_False);

  assert(S.trie.accepting_place.hor == &S.trie.root);
  assert(S.trie.accepting_place.hor_ix == 0);
  assert(S.trie.accepting_place.ver_ix == 0);
  assert(S.trie.accepting_rear_visit_level == 0);
  assert(S.trie.accepting_van_visit_level == 0);
  assert(S.trie.accepting_reusable_van == &S.trie.root_new_vans[0]);
  assert(S.trie.accepting_reusable_rear == &S.trie.root_new_rears[0]);
}


void test_chain4() {
  Solver S;
  std::unordered_set<unsigned> finals;
  assert(init_test(S, 4, finals) == l_Undef);
  assert(S.value(Lit(0)) == l_Undef);
  assert(S.value(Lit(1)) == l_Undef);
  assert(S.value(Lit(2)) == l_Undef);
  assert(S.value(Lit(3)) == l_Undef);

  assert(S.trie.reset(S) == NULL);

  S.enqueue(~Lit(2));
  assert(S.propagate() == NULL);

  assert(S.value(Lit(0)) == l_Undef);
  assert(S.value(Lit(1)) == l_Undef);
  assert(S.value(Lit(2)) == l_False);
  assert(S.value(Lit(3)) == l_Undef);

  S.enqueue(~Lit(3));
  assert(S.propagate() == NULL);

  assert(S.value(Lit(0)) == l_Undef);
  assert(S.value(Lit(1)) == l_Undef);
  assert(S.value(Lit(2)) == l_False);
  assert(S.value(Lit(3)) == l_False);

  S.enqueue(~Lit(1));
  assert(S.propagate() == NULL);

  assert(S.value(Lit(0)) == l_True);
  assert(S.value(Lit(1)) == l_False);
  assert(S.value(Lit(2)) == l_False);
  assert(S.value(Lit(3)) == l_False);

  assert(S.trie.accepting_place.hor == &S.trie.root);
  assert(S.trie.accepting_place.hor_ix == 0);
  assert(S.trie.accepting_place.ver_ix == IX_NULL);
  assert(S.trie.accepting_rear_visit_level == 0);
  assert(S.trie.accepting_van_visit_level == 0);
  assert(S.trie.accepting_reusable_van == &S.trie.root_new_vans[0]);
  assert(S.trie.accepting_reusable_rear == &S.trie.root_new_rears[0]);
}


void test_chair() {
  Solver S;
  std::unordered_set<unsigned> finals({3, 4, 5});
  assert(init_test(S, 6, finals) == l_Undef);
  assert(S.value(Lit(0)) == l_Undef);
  assert(S.value(Lit(1)) == l_Undef);
  assert(S.value(Lit(2)) == l_Undef);
  assert(S.value(Lit(3)) == l_Undef);

  S.trie.root.elems[0].hors[0].hor = new HorLine{Place{&S.trie.root, 0, 0}};
  S.trie.root.elems[0].hors[0].hor->elems.emplace_back(Lit(3));
  S.trie.root.elems[0].hors[0].hor->elems[0].hors.emplace_back(Lit(4), 2);
  S.trie.root.elems[0].hors[0].hor->elems[0].hors.emplace_back(Lit(5), 3);
  assert(S.trie.reset(S) == NULL);

  S.enqueue(~Lit(1));
  S.enqueue(~Lit(4));
  assert(S.propagate() == NULL);

  assert(S.value(Lit(0)) == l_Undef);
  assert(S.value(Lit(1)) == l_False);
  assert(S.value(Lit(2)) == l_Undef);
  assert(S.value(Lit(3)) == l_Undef);
  assert(S.value(Lit(4)) == l_False);
  assert(S.value(Lit(5)) == l_Undef);

  S.enqueue(~Lit(0));
  assert(S.propagate() == NULL);

  assert(S.value(Lit(0)) == l_False);
  assert(S.value(Lit(1)) == l_False);
  assert(S.value(Lit(2)) == l_True);
  assert(S.value(Lit(3)) == l_Undef);
  assert(S.value(Lit(4)) == l_False);
  assert(S.value(Lit(5)) == l_Undef);

  assert(S.trie.accepting_place.hor == &S.trie.root);
  assert(S.trie.accepting_place.hor_ix == 0);
  assert(S.trie.accepting_place.ver_ix == 1);
  assert(S.trie.accepting_rear_visit_level == 0);
  assert(S.trie.accepting_van_visit_level == 0);
  assert(S.trie.accepting_reusable_van == &S.trie.root_new_vans[0]);
  assert(S.trie.accepting_reusable_rear == &S.trie.root_new_rears[0]);

  S.enqueue(~Lit(3));
  S.enqueue(~Lit(5));
  Reason *conflict_reason = S.propagate();
  assert(conflict_reason != NULL);

  vec<Lit> out_reason;
  conflict_reason->calcReason(S, lit_Undef, out_reason);

  std::unordered_set<int> out_reason_set;
  for (int i = 0; i < out_reason.size(); i++) out_reason_set.insert(index(out_reason[i]));
  assert(out_reason_set == std::unordered_set({
    index(~Lit(0)),
    index(~Lit(3)),
    index(~Lit(4)),
    index(~Lit(5))
  }));
}



int main(int argc, char **argv) {
  test_init_twolit();
  test_init_onelit();
  test_twolit_conflict();
  test_twolit_jump();
  test_twolit_van_accept();
  test_twolit_van_exhaust();
  test_twolit_rear_accept_then_van_accept();
  test_twolit_rear_accept_then_van_exhaust();
  test_L();
  test_cap();
  test_chair();
  return 0;
}
