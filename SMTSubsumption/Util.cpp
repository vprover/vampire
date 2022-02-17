/*
 * Util.cpp
 * Copyright (C) 2022 Jakob Rath <git@jakobrath.eu>
 *
 * Distributed under terms of the MIT license.
 */

#include "Util.hpp"
#include "Lib/STL.hpp"
#include "Debug/Assertion.hpp"

using namespace Kernel;



bool checkClauseEquality(Literal const* const lits1[], unsigned len1, Literal const* const lits2[], unsigned len2)
{
  if (len1 != len2) {
    return false;
  }
  // Copy given literals so we can sort them
  vvector<Literal const*> c1(lits1, lits1 + len1);
  vvector<Literal const*> c2(lits2, lits2 + len2);
  // The equality tests only make sense for shared literals
  std::for_each(c1.begin(), c1.end(), [](Literal const* lit) { ASS(lit->shared()); });
  std::for_each(c2.begin(), c2.end(), [](Literal const* lit) { ASS(lit->shared()); });
  // Sort input by pointer value
  // NOTE: we use std::less<> because the C++ standard guarantees it is a total order on pointer types.
  //       (the built-in operator< is not required to be a total order for pointer types.)
  std::less<Literal const*> const lit_ptr_less{};
  std::sort(c1.begin(), c1.end(), lit_ptr_less);
  std::sort(c2.begin(), c2.end(), lit_ptr_less);
  // Finally check the equality
  return c1 == c2;
}



bool checkClauseEquality(Clause* const cl1, Clause* const cl2)
{
  return checkClauseEquality(cl1->literals(), cl1->length(), cl2->literals(), cl2->length());
}
