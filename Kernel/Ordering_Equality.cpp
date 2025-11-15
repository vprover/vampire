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
 * @file Ordering_Equality.cpp
 * Implements class Ordering_Equality.
 */

#include "Term.hpp"

#include "Ordering.hpp"

namespace Kernel
{

Ordering::Result Ordering::compareEqualities(Literal* eq1, Literal* eq2) const
{
  ASS(eq1->isEquality());
  ASS(eq2->isEquality());

  auto s1=*eq1->nthArgument(0);
  auto s2=*eq1->nthArgument(1);
  auto t1=*eq2->nthArgument(0);
  auto t2=*eq2->nthArgument(1);

  if (s1 == t1) {
    return compare(s2,t2);
  }
  if (s1 == t2) {
    return compare(s2,t1);
  }
  if (s2 == t1) {
    return compare(s1,t2);
  }
  if (s2 == t2) {
    return compare(s1,t1);
  }

  auto cmp = compare(s1,t1);
  switch(cmp) {
  case GREATER:
    return compare_s1Gt1(s1,s2,t1,t2);
  case INCOMPARABLE:
    return compare_s1It1(s1,s2,t1,t2);
  case LESS:
    return reverse(compare_s1Gt1(t1,t2,s1,s2));
  default:
    ASSERTION_VIOLATION;
  }
}

/**
 * Return the result of comparison of literals s1=s2 and t1=t2, assuming s1 > t1
 */
Ordering::Result Ordering::compare_s1Gt1(TermList s1,TermList s2,TermList t1,TermList t2) const
{
  ASS_EQ(compare(s1,t1), GREATER);

  switch(compare(s2,t2)) {
  case GREATER:
    return GREATER;
  case INCOMPARABLE:
    return compare_s1Gt1_s2It2(s1,s2,t1,t2);
  case LESS:
    return compare_s1Gt1_s2Lt2(s1,s2,t1,t2);
  default:
    ASSERTION_VIOLATION;
  }
}

/**
 * Return the result of literal comparison assuming s1 inc t1
 */
Ordering::Result Ordering::compare_s1It1(TermList s1,TermList s2,TermList t1,TermList t2) const
{
  ASS_EQ(compare(s1,t1), INCOMPARABLE);

  switch(compare(s2,t2)) {
  case GREATER:
    return compare_s1Gt1_s2It2(s2,s1,t2,t1);
  case INCOMPARABLE:
    return compare_s1It1_s2It2(s1,s2,t1,t2);
  case LESS:
    return reverse(compare_s1Gt1_s2It2(t2,t1,s2,s1));
  default:
    ASSERTION_VIOLATION;
  }
}

/**
 * Return the result of literal comparison assuming s1 inc t1 and s2 inc t2
 */
Ordering::Result Ordering::compare_s1It1_s2It2(TermList s1,TermList s2,TermList t1,TermList t2) const
{
  ASS_EQ(compare(s1,t1), INCOMPARABLE);
  ASS_EQ(compare(s2,t2), INCOMPARABLE);

  switch(compare(s1,t2)) {
  case GREATER:
    return compare_s1Gt1_s1It2_s2It1(s1,s2,t2,t1);
  case INCOMPARABLE:
    return INCOMPARABLE;
  case LESS:
    return reverse(compare_s1Gt1_s1It2_s2It1(t2,t1,s1,s2));
  default:
    ASSERTION_VIOLATION;
  }
}

/**
 * Return the result of literal comparison assuming s1 > t1 and s2 inc t2
 */
Ordering::Result Ordering::compare_s1Gt1_s2It2(TermList s1,TermList s2,TermList t1,TermList t2) const
{
  ASS_EQ(compare(s1,t1), GREATER);
  ASS_EQ(compare(s2,t2), INCOMPARABLE);

  switch(compare(s1,t2)) {
  case GREATER:
    return GREATER;
  case INCOMPARABLE:
    return INCOMPARABLE;
  case LESS:
    ASS_NEQ(compare(s2,t1), LESS); //would cause s2<t2 by transitivity t2>s1>t1>s2 or t2>=s1>t1>s2
    ASS_EQ(compare(t1,t2), LESS); //transitivity through s1
    return INCOMPARABLE;
  default:
    ASSERTION_VIOLATION;
  }
}

/**
 * Return the result of literal comparison assuming s1 > t1 and s2 < t2
 */
Ordering::Result Ordering::compare_s1Gt1_s2Lt2(TermList s1,TermList s2,TermList t1,TermList t2) const
{
  ASS_EQ(compare(s1,t1), GREATER);
  ASS_EQ(compare(s2,t2), LESS);

  switch(compare(s1,t2)) {
  case GREATER:
    ASS_EQ(compare(s1,s2), GREATER); //transitivity through t2
    return GREATER;
  case INCOMPARABLE:
    return INCOMPARABLE;
  case LESS:
    ASS_EQ(compare(t1,t2), LESS); //transitivity through t2
    return LESS;
  default:
    ASSERTION_VIOLATION;
  }
}

/**
 * Return the result of literal comparison assuming s1 > t1, s1 inc t2, s2 inc t1
 */
Ordering::Result Ordering::compare_s1Gt1_s1It2_s2It1(TermList s1,TermList s2,TermList t1,TermList t2) const
{
  ASS_EQ(compare(s1,t1), GREATER);
  ASS_EQ(compare(s1,t2), INCOMPARABLE);
  ASS_EQ(compare(s2,t1), INCOMPARABLE);

  switch(compare(s2,t2)) {
  case GREATER:
    return GREATER;
  case INCOMPARABLE:
  case LESS:
    return INCOMPARABLE;
  default:
    ASSERTION_VIOLATION;
  }
}

} // namespace Kernel
