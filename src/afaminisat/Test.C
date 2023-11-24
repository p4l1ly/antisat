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
  if (S.trie.reset(S)) return l_False;
  return l_Undef;
}


void test_init_twolit() {
  Solver S;
  assert(init_test(S, 2) == l_Undef);
  assert(S.value(Lit(0)) == l_Undef);
  assert(S.value(Lit(1)) == l_Undef);
}


void test_init_onelit() {
  Solver S;
  assert(init_test(S, 1) == l_Undef);
  assert(S.value(Lit(0)) == l_True);
}


void test_twolit_jump() {
  Solver S;
  assert(init_test(S, 2) == l_Undef);
  assert(S.value(Lit(0)) == l_Undef);
  assert(S.value(Lit(1)) == l_Undef);

  S.enqueue(~Lit(0));
  S.propagate();
  assert(S.value(Lit(0)) == l_False);
  assert(S.value(Lit(1)) == l_True);
}

void test_twolit_van_accept() {
  Solver S;
  assert(init_test(S, 2) == l_Undef);
  assert(S.value(Lit(0)) == l_Undef);
  assert(S.value(Lit(1)) == l_Undef);

  S.enqueue(Lit(1));
  S.propagate();
  assert(S.value(Lit(0)) == l_Undef);
  assert(S.value(Lit(1)) == l_True);

  S.enqueue(~Lit(0));
  S.propagate();
  assert(S.value(Lit(0)) == l_False);
  assert(S.value(Lit(1)) == l_True);
}

void test_twolit_van_exhaust() {
  Solver S;
  assert(init_test(S, 2) == l_Undef);
  assert(S.value(Lit(0)) == l_Undef);
  assert(S.value(Lit(1)) == l_Undef);

  S.enqueue(~Lit(1));
  S.propagate();
  assert(S.value(Lit(0)) == l_True);
  assert(S.value(Lit(1)) == l_False);
}

void test_twolit_rear_accept_then_van_accept() {
  Solver S;
  assert(init_test(S, 2) == l_Undef);
  assert(S.value(Lit(0)) == l_Undef);
  assert(S.value(Lit(1)) == l_Undef);

  S.enqueue(Lit(0));
  S.propagate();
  assert(S.value(Lit(0)) == l_True);
  assert(S.value(Lit(1)) == l_Undef);

  S.enqueue(Lit(1));
  S.propagate();
  assert(S.value(Lit(0)) == l_True);
  assert(S.value(Lit(1)) == l_True);
}

void test_twolit_rear_accept_then_van_exhaust() {
  Solver S;
  assert(init_test(S, 2) == l_Undef);
  assert(S.value(Lit(0)) == l_Undef);
  assert(S.value(Lit(1)) == l_Undef);

  S.enqueue(Lit(0));
  S.propagate();
  assert(S.value(Lit(0)) == l_True);
  assert(S.value(Lit(1)) == l_Undef);

  S.enqueue(~Lit(1));
  S.propagate();
  assert(S.value(Lit(0)) == l_True);
  assert(S.value(Lit(1)) == l_False);
}


int main(int argc, char **argv) {
  test_init_twolit();
  test_init_onelit();
  test_twolit_jump();
  test_twolit_van_accept();
  test_twolit_van_exhaust();
  test_twolit_rear_accept_then_van_accept();
  test_twolit_rear_accept_then_van_exhaust();
  return 0;
}
