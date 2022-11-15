cmake_minimum_required(VERSION 3.16)

project(
  afaminisat
  VERSION 0.1.0
  DESCRIPTION "MiniSAT adjusted and optimized to solve AFA emptiness"
  LANGUAGES CXX
)

find_package(CapnProto REQUIRED)

set(CMAKE_C_FLAGS ${CMAKE_C_FLAGS})
set(CMAKE_CXX_FLAGS ${CMAKE_CXX_FLAGS})

add_executable(
  afaminisat
  src/afaminisat/Main.C
  src/afaminisat/Solver.C
  src/afaminisat/Trie.C
  src/afaminisat/SupQ.C
  src/afaminisat/Constraints.C
  src/afaminisat/CnfAfa.capnp.C
)
target_link_libraries(
    afaminisat PRIVATE CapnProto::capnp
)
set_property(TARGET afaminisat PROPERTY CXX_STANDARD 20)
