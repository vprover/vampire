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
 * @file Matcher.hpp
 * Defines class HOL::Matcher.
 */

#ifndef __HOL_Matcher__
#define __HOL_Matcher__

#include "Forwards.hpp"

#include "Kernel/TypedTermList.hpp"
#include "Kernel/Substitution.hpp"

namespace Kernel::HOL {

class Matcher
{
public:
  Matcher(TypedTermList base, TypedTermList instance) {
    todo.emplace(base, instance);
  }

  bool hasNext();
  const Substitution& next() const;

  static bool matches(TypedTermList base, TypedTermList instance);

private:
  Stack<std::pair<TypedTermList, TypedTermList>> todo;
  Substitution subst;
};

}

#endif /* __HOL_Matcher__ */
