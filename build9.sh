cmake -S . -B buildafa_trie_heap_reverseadd -DCMAKE_BUILD_TYPE=Release \
  -DMODE=AFA_TRIE_HEAP_HEAP \
  -DSTRENGTHENCC=ON \
  -DNO_POSNEG_OUTPUTS=ON \
  -DONE_ORDER=OFF \
  -DNO_OUTPUTS=OFF \
  -DCELL_CONTAINER=SET \
  -DNEW_ANALYZE=OFF \
  -DOPTIONAL_CLAUSES=OFF \
  -DNOGUESS_VARS=OFF \
  -DALL_SOLO=OFF \
  -DREVERSE_ADD=ON \
  ;
cmake --build buildafa_trie_heap_reverseadd

cmake -S . -B buildafa_trie_heap_setsuccone -DCMAKE_BUILD_TYPE=Release \
  -DMODE=AFA_TRIE_HEAP_HEAP \
  -DSTRENGTHENCC=ON \
  -DNO_POSNEG_OUTPUTS=ON \
  -DONE_ORDER=OFF \
  -DNO_OUTPUTS=OFF \
  -DCELL_CONTAINER=SET \
  -DNEW_ANALYZE=OFF \
  -DOPTIONAL_CLAUSES=OFF \
  -DNOGUESS_VARS=OFF \
  -DALL_SOLO=OFF \
  -DSET_SUCCESSOR_ONE=ON \
  ;
cmake --build buildafa_trie_heap_setsuccone

cmake -S . -B buildafa_trie_heap_printsattimes -DCMAKE_BUILD_TYPE=Release \
  -DMODE=AFA_TRIE_HEAP_HEAP \
  -DSTRENGTHENCC=ON \
  -DNO_POSNEG_OUTPUTS=ON \
  -DONE_ORDER=OFF \
  -DNO_OUTPUTS=OFF \
  -DCELL_CONTAINER=SET \
  -DNEW_ANALYZE=OFF \
  -DOPTIONAL_CLAUSES=OFF \
  -DNOGUESS_VARS=OFF \
  -DALL_SOLO=OFF \
  -DPRINT_SAT_TIMES=ON \
  ;
cmake --build buildafa_trie_heap_printsattimes

cmake -S . -B buildafa_clause_heap_printsattimes -DCMAKE_BUILD_TYPE=Release \
  -DMODE=AFA_CLAUSE_HEAP_HEAP \
  -DSTRENGTHENCC=ON \
  -DNO_POSNEG_OUTPUTS=ON \
  -DONE_ORDER=OFF \
  -DNO_OUTPUTS=OFF \
  -DCELL_CONTAINER=SET \
  -DNEW_ANALYZE=OFF \
  -DOPTIONAL_CLAUSES=OFF \
  -DNOGUESS_VARS=OFF \
  -DPRINT_SAT_TIMES=ON \
  ;
cmake --build buildafa_clause_heap_printsattimes

cmake -S . -B buildafa_trie_heap_reverseadd_printsattimes -DCMAKE_BUILD_TYPE=Release \
  -DMODE=AFA_TRIE_HEAP_HEAP \
  -DSTRENGTHENCC=ON \
  -DNO_POSNEG_OUTPUTS=ON \
  -DONE_ORDER=OFF \
  -DNO_OUTPUTS=OFF \
  -DCELL_CONTAINER=SET \
  -DNEW_ANALYZE=OFF \
  -DOPTIONAL_CLAUSES=OFF \
  -DNOGUESS_VARS=OFF \
  -DALL_SOLO=OFF \
  -DREVERSE_ADD=ON \
  -DPRINT_SAT_TIMES=ON \
  ;
cmake --build buildafa_trie_heap_reverseadd_printsattimes

cmake -S . -B buildafa_trie_heap_setsuccone_printsattimes -DCMAKE_BUILD_TYPE=Release \
  -DMODE=AFA_TRIE_HEAP_HEAP \
  -DSTRENGTHENCC=ON \
  -DNO_POSNEG_OUTPUTS=ON \
  -DONE_ORDER=OFF \
  -DNO_OUTPUTS=OFF \
  -DCELL_CONTAINER=SET \
  -DNEW_ANALYZE=OFF \
  -DOPTIONAL_CLAUSES=OFF \
  -DNOGUESS_VARS=OFF \
  -DALL_SOLO=OFF \
  -DSET_SUCCESSOR_ONE=ON \
  -DPRINT_SAT_TIMES=ON \
  ;
cmake --build buildafa_trie_heap_setsuccone_printsattimes
