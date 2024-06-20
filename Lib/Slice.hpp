/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#ifndef SLICE_HPP
#define SLICE_HPP

namespace Lib {


/**
 * A Slice instance represents a contiguous range of memory.
 */
template <typename T>
class Slice
{
public:
  Slice(T *begin, T *end) : _begin(begin), _end(end) {}

  unsigned size() const { return _end - _begin; };

  T operator[](unsigned i) const
  {
    ASS_L(i, size());
    return _begin[i];
  }

  const T &back() const
  {
    ASS_G(size(), 0);
    return *(_end - 1);
  }

  T *begin() const { return _begin; }
  T *end() const { return _end; }

private:
  T *_begin;
  T *_end;
};


} // namespace Lib

#endif
