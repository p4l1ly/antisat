cmake_minimum_required(VERSION 3.17)

project(
  afaminisat
  VERSION 0.1.0
  DESCRIPTION "MiniSAT adjusted and optimized to solve AFA emptiness"
  LANGUAGES CXX
)

find_package(CapnProto CONFIG REQUIRED)

set(CAPNPC_SRC_PREFIX "${CMAKE_CURRENT_SOURCE_DIR}/schema" CACHE STRING "" FORCE)
set(CAPNPC_OUTPUT_DIR "${CMAKE_CURRENT_BINARY_DIR}/afa_schema/schema" CACHE STRING "" FORCE)
file(MAKE_DIRECTORY "${CAPNPC_OUTPUT_DIR}")

capnp_generate_cpp(afaSources afaHeaders schema/cnfafa.capnp)

add_executable(
  afaminisat
  src/afaminisat/Main.C
  src/afaminisat/Solver.C
  src/afaminisat/Trie.C
  src/afaminisat/SupQ.C
  src/afaminisat/Constraints.C
  ${afaSources}
)
target_include_directories(afaminisat PRIVATE "${CMAKE_CURRENT_BINARY_DIR}/afa_schema")
target_link_libraries(afaminisat PRIVATE z)
set_property(TARGET afaminisat PROPERTY CXX_STANDARD 20)
