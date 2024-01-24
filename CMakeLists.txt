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

option(NEW_VARORDER "use new varorder" OFF)
option(NEW_ANALYZE "use new analyze function" OFF)
option(STRENGTHENCC "use strengthenCC" OFF)

# add_executable(
#   afaminisat
#   src/afaminisat/Main.C
#   src/afaminisat/Solver.C
#   src/afaminisat/Trie.C
#   src/afaminisat/SupQ.C
#   src/afaminisat/Constraints.C
#   src/afaminisat/LogList.C
#   src/afaminisat/VarOrder.C
# )
# set_property(TARGET afaminisat PROPERTY CXX_STANDARD 20)

set(TRIESAT_DEPS "")
set(TRIESAT_DEPS "${TRIESAT_DEPS};src/afaminisat/MainSat.C")
set(TRIESAT_DEPS "${TRIESAT_DEPS};src/afaminisat/Solver.C")
set(TRIESAT_DEPS "${TRIESAT_DEPS};src/afaminisat/Trie.C")
set(TRIESAT_DEPS "${TRIESAT_DEPS};src/afaminisat/SupQ.C")
set(TRIESAT_DEPS "${TRIESAT_DEPS};src/afaminisat/Constraints.C")
set(TRIESAT_DEPS "${TRIESAT_DEPS};src/afaminisat/LogList.C")

if (NEW_VARORDER)
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DNEW_VARORDER")
  set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS_DEBUG} -DNEW_VARORDER")
  set(TRIESAT_DEPS "${TRIESAT_DEPS};src/afaminisat/VarOrder.C")
endif()

if (NEW_ANALYZE)
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DNEW_ANALYZE")
  set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS_DEBUG} -DNEW_ANALYZE")
endif()

add_executable(
  triesat
  ${TRIESAT_DEPS}
)
set_property(TARGET triesat PROPERTY CXX_STANDARD 20)
# target_include_directories(triesat PRIVATE ${LIBLZMA_INCLUDE_DIRS})
# target_link_libraries(afaminisat PRIVATE ${LIBLZMA_LIBRARIES})
