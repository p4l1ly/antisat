cmake_minimum_required(VERSION 3.16)

project(
  afaminisat
  VERSION 0.1.0
  DESCRIPTION "MiniSAT adjusted and optimized to solve AFA emptiness"
  LANGUAGES CXX
)

# find_package(LibLZMA REQUIRED)

set(CMAKE_C_FLAGS ${CMAKE_C_FLAGS})
set(CMAKE_CXX_FLAGS ${CMAKE_CXX_FLAGS})
set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS_DEBUG} -DMY_DEBUG")

set(FLAGS "")

option(NEW_ANALYZE "use new analyze function" ON)
option(STRENGTHENCC "use strengthenCC" ON)
option(SOLIDIFY "solidify trie before SAT" ON)
option(ALL_SOLO "don't use rear/van guards but only solo guards (limited unit propagation)" OFF)
option(WATCH_CLAUSE_WATCH "input clauses have impact on watch bubble order" OFF)
option(WATCH_LEARNT_WATCH "learnt clauses have impact on watch bubble order" OFF)

set(MODE "${MODE}" CACHE STRING "modus_operandi" FORCE)

set(TRIESAT_DEPS "")
set(TRIESAT_DEPS "${TRIESAT_DEPS};src/afaminisat/MainSat.C")
set(TRIESAT_DEPS "${TRIESAT_DEPS};src/afaminisat/Solver.C")
set(TRIESAT_DEPS "${TRIESAT_DEPS};src/afaminisat/Constraints.C")
set(TRIESAT_DEPS "${TRIESAT_DEPS};src/afaminisat/LogList.C")
set(TRIESAT_DEPS "${TRIESAT_DEPS};src/afaminisat/VarOrder.C")
set(TRIESAT_DEPS "${TRIESAT_DEPS};src/afaminisat/watch_varorder/VarOrder.C")
set(TRIESAT_DEPS "${TRIESAT_DEPS};src/afaminisat/finish_varorder/VarOrder.C")

set(FLAGS "${FLAGS} -D${MODE}")

if (MODE STREQUAL "SAT_TRIE_HEAP")
  set(USE_TRIE ON)
  set(FLAGS "${FLAGS} -DHEAP_VARORDER")
elseif (MODE STREQUAL "SAT_TRIE_BUBBLE")
  set(USE_TRIE ON)
  set(FLAGS "${FLAGS} -DBUBBLE_VARORDER")
elseif (MODE STREQUAL "SAT_TRIE_WATCH")
  set(USE_TRIE ON)
  set(FLAGS "${FLAGS} -DWATCH_VARORDER")
elseif (MODE STREQUAL "SAT_CLAUSE_HEAP")
  set(USE_TRIE OFF)
  set(FLAGS "${FLAGS} -DHEAP_VARORDER")
elseif (MODE STREQUAL "SAT_CLAUSE_BUBBLE")
  set(USE_TRIE OFF)
  set(FLAGS "${FLAGS} -DBUBBLE_VARORDER")
elseif (MODE STREQUAL "SAT_CLAUSE_WATCH")
  set(USE_TRIE OFF)
  set(FLAGS "${FLAGS} -DWATCH_VARORDER")
  set(FLAGS "${FLAGS} -DWATCH_CLAUSE_WATCH")
else()
  message(FATAL_ERROR "Unknown MODE ${MODE}")
endif()

if (USE_TRIE)
  set(TRIESAT_DEPS "${TRIESAT_DEPS};src/afaminisat/Trie.C")
  set(FLAGS "${FLAGS} -DUSE_TRIE")
  set(FLAGS "${FLAGS} -DTRIE_FOR_INPUT")
endif()

if (NEW_ANALYZE)
  set(FLAGS "${FLAGS} -DNEW_ANALYZE")
endif()

if (ALL_SOLO AND USE_TRIE)
  set(FLAGS "${FLAGS} -DALL_SOLO")
endif()

if (STRENGTHENCC)
  set(FLAGS "${FLAGS} -DSTRENGTHENCC")
endif()

if (SOLIDIFY AND USE_TRIE)
  set(FLAGS "${FLAGS} -DSOLIDIFY")
endif()

if (WATCH_LEARNT_WATCH)
  set(FLAGS "${FLAGS} -DWATCH_LEARNT_WATCH")
endif()

if (WATCH_CLAUSE_WATCH)
  set(FLAGS "${FLAGS} -DWATCH_CLAUSE_WATCH")
endif()

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${FLAGS}")
set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS_DEBUG} ${FLAGS}")

add_executable(
  triesat
  ${TRIESAT_DEPS}
)
set_property(TARGET triesat PROPERTY CXX_STANDARD 20)
