#include "LogList.h"

pair<uint32_t, uint32_t> _LogList_stage_ix(uint32_t ix) {
  ++ix;

  // get the position of the highest set bit (binary logarithm)
  unsigned position;
  asm ("bsrl %1, %0" : "=r" (position) : "r" (ix));

  return pair(position, ix & ~(1 << position));
}
