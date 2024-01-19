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

add_executable(
  afaminisat
  src/afaminisat/Main.C
  src/afaminisat/Solver.C
  src/afaminisat/Trie.C
  src/afaminisat/SupQ.C
  src/afaminisat/Constraints.C
  src/afaminisat/LogList.C
  src/afaminisat/VarOrder.C
)
set_property(TARGET afaminisat PROPERTY CXX_STANDARD 20)

add_executable(
  triesat
  src/afaminisat/MainSat.C
  src/afaminisat/Solver.C
  src/afaminisat/Trie.C
  src/afaminisat/SupQ.C
  src/afaminisat/Constraints.C
  src/afaminisat/LogList.C
  src/afaminisat/VarOrder.C
)
set_property(TARGET triesat PROPERTY CXX_STANDARD 20)
# target_include_directories(triesat PRIVATE ${LIBLZMA_INCLUDE_DIRS})
# target_link_libraries(afaminisat PRIVATE ${LIBLZMA_LIBRARIES})
