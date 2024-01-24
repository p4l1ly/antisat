#ifndef LogList_h
#define LogList_h

#include <iostream>
#include <utility>
#include <vector>
#include <stdint.h>
#include <cassert>

using std::pair;
using std::vector;

// First array will have size 2^GRANULARITY, second 2*(2^GRANULARITY), etc.
#define GRANULARITY 3

pair<uint32_t, uint32_t> _LogList_stage_ix(uint32_t ix);

#define ITER_LOGLIST(self, T, x, fn) { \
  if ((self)._size != 0) { \
    pair<uint32_t, uint32_t> stageix = _LogList_stage_ix((self)._size); \
    if (stageix.first != 0) { \
      for (unsigned __i = 0; __i < stageix.first; ++__i) { \
        T* stage = (self)._stages[__i]; \
        for (unsigned j = 0; j < (1 << GRANULARITY) << __i; ++j) { \
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

#define ITER_LOGLIST_BACK(self, T, x, fn) { \
  if ((self)._size != 0) { \
    pair<uint32_t, uint32_t> stageix = _LogList_stage_ix((self)._size); \
    if (stageix.second != 0) { \
      T* stage = (self)._stages[stageix.first]; \
      for (unsigned __j = stageix.second; __j;) { \
        --__j; \
        T& x = stage[__j]; \
        fn \
      } \
    } \
    if (stageix.first != 0) { \
      for (unsigned __i = stageix.first; __i;) { \
        --__i; \
        T* stage = (self)._stages[__i]; \
        for (unsigned __j = (1 << GRANULARITY) << __i; __j;) { \
          --__j; \
          T& x = stage[__j]; \
          fn \
        } \
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

  void clear() {
    ITER_LOGLIST(*this, T, x, x.~T(););
    _size = 0;
  }

  template <typename... Args>
  T& emplace_back(Args&&... args) {
    pair<uint32_t, uint32_t> stageix = _LogList_stage_ix(_size);
    if (_stages.size() == stageix.first) {
      assert(_size + (1 << GRANULARITY) == (1 << GRANULARITY) << stageix.first);
      _stages.push_back(static_cast<T*>(::operator new(sizeof(T) * ((1 << GRANULARITY) << stageix.first))));
    }
    T& ref = _stages[stageix.first][stageix.second];
    ++_size;
    new (&ref) T(std::forward<Args>(args)...);
    return ref;
  }

  T& push_back(const T & t) { return emplace_back(t); }
  T& push_back(T && t) { return emplace_back(std::move(t)); }

  inline void clear_nodestroy() {
    _size = 0;
  }

  uint32_t size() { return _size; }

  ~LogList() {
    ITER_LOGLIST(*this, T, x, x.~T(););
    for (unsigned i = 0; i < _stages.size(); ++i) {
      ::operator delete(_stages[i]);
    }
  }
};

#endif
