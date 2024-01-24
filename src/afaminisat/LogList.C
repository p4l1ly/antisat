#include "LogList.h"

pair<uint32_t, uint32_t> _LogList_stage_ix(uint32_t ix) {
  // std::cout << "IX " << ix;
  unsigned granularity_modulo = ix & ((1 << GRANULARITY) - 1);
  ix >>= GRANULARITY;
  ++ix;

  // get the position of the highest set bit (binary logarithm)
  unsigned position;
  asm ("bsrl %1, %0" : "=r" (position) : "r" (ix));

  // std::cout << " " << position;
  // std::cout << " " << (((ix & ~(1 << position)) << GRANULARITY) | granularity_modulo) << std::endl;
  return pair(position, ((ix & ~(1 << position)) << GRANULARITY) | granularity_modulo);
}
