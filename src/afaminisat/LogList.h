#ifndef LogList_h
#define LogList_h

#include <iostream>
#include <utility>
#include <vector>
#include <stdint.h>

using std::pair;
using std::vector;

pair<uint32_t, uint32_t> _LogList_stage_ix(uint32_t ix);

#define ITER_LOGLIST(self, T, fn) { \
  if ((self)._size != 0) { \
    pair<uint32_t, uint32_t> stageix = _LogList_stage_ix((self)._size); \
    if (stageix.first != 0) { \
      for (unsigned i = 0; i < stageix.first; ++i) { \
        T* stage = (self)._stages[i]; \
        for (unsigned j = 0; j < (1 << i); ++j) { \
          T& x = stage[j]; \
          fn \
        } \
      } \
    } \
    if (stageix.second != 0) { \
      T* stage = (self)._stages[stageix.first]; \
      for (unsigned j = 0; j < stageix.second; ++j) { \
        T& x = stage[j]; \
        fn \
      } \
    } \
  } \
}

template<class T>
class LogList {
public:
  uint32_t _size;
  vector<T*> _stages;

  LogList() : _size(0), _stages() {}

  LogList(LogList&& old) noexcept
  : _size(old._size)
  , _stages(std::move(old._stages))
  {
    old._size = 0;
  }

  LogList(LogList& old) = delete;

  T& operator[] (uint32_t index) {
    pair<uint32_t, uint32_t> stageix = _LogList_stage_ix(index);
    return _stages[stageix.first][stageix.second];
  }

  T& push_back(T&& elem) {
    pair<uint32_t, uint32_t> stageix = _LogList_stage_ix(_size);
    if (_stages.size() == stageix.first) {
      _stages.push_back(static_cast<T*>(::operator new(sizeof(T) * (1 << stageix.first))));
    }
    T& ref = _stages[stageix.first][stageix.second];
    new (&ref) T(elem);
    ++_size;
    return ref;
  }
  void clear() {
    ITER_LOGLIST(*this, T, x.~T(););
    _size = 0;
  }
  inline void clear_nodestroy() {
    _size = 0;
  }
  uint32_t size() { return _size; }

  ~LogList() {
    ITER_LOGLIST(*this, T, x.~T(););
    for (unsigned i = 0; i < _stages.size(); ++i) {
      ::operator delete(_stages[i]);
    }
  }
};

#endif
