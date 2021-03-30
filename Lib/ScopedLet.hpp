/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file ScopedLet.hpp
 * Defines class ScopedLet.
 */

#ifndef __ScopedLet__
#define __ScopedLet__

namespace Lib {

template<typename T>
class ScopedLet {
public:
  ScopedLet(T& ref, T value)
  : _ref(ref), _originalValue(ref)
  {
    _ref = value;
  }

  ~ScopedLet()
  {
    _ref = _originalValue;
  }

private:
  T& _ref;
  T _originalValue;
};

}

#endif // __ScopedLet__
