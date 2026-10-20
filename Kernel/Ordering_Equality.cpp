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

Ordering::Result Ordering::compareEqualities(AppliedTerm aeq1, AppliedTerm aeq2) const
{
  auto eq1 = static_cast<Literal*>(aeq1.term.term());
  auto eq2 = static_cast<Literal*>(aeq2.term.term());

  AppliedTerm s1(eq1->termArg(0), aeq1);
  AppliedTerm s2(eq1->termArg(1), aeq1);
  AppliedTerm t1(eq2->termArg(0), aeq2);
  AppliedTerm t2(eq2->termArg(1), aeq2);

  auto s1_t1 = compare(s1, t1);
  if (s1_t1 == EQUAL) {
    return compare(s2,t2);
  }
  auto s1_t2 = compare(s1, t2);
  if (s1_t2 == EQUAL) {
    return compare(s2,t1);
  }
  auto s2_t1 = compare(s2, t1);
  if (s2_t1 == EQUAL) {
    return compare(s1,t2);
  }
  auto s2_t2 = compare(s2, t2);
  if (s2_t2 == EQUAL) {
    return compare(s1,t1);
  }

  switch(s1_t1) {
  case GREATER:
    return compare_s1Gt1(s1_t1,s1_t2,s2_t1,s2_t2);
  case INCOMPARABLE:
    return compare_s1It1(s1_t1,s1_t2,s2_t1,s2_t2);
  case LESS:
    return reverse(compare_s1Gt1(reverse(s1_t1),reverse(s1_t2),reverse(s2_t1),reverse(s2_t2)));
  default:
    ASSERTION_VIOLATION;
  }
}

/**
 * Return the result of comparison of literals s1=s2 and t1=t2, assuming s1 > t1
 */
Ordering::Result Ordering::compare_s1Gt1(Result s1_t1, Result s1_t2, Result s2_t1, Result s2_t2) const
{
  ASS_EQ(s1_t1, GREATER);

  switch(s2_t2) {
  case GREATER:
    return GREATER;
  case INCOMPARABLE:
    return compare_s1Gt1_s2It2(s1_t1,s1_t2,s2_t1,s2_t2);
  case LESS:
    return compare_s1Gt1_s2Lt2(s1_t1,s1_t2,s2_t1,s2_t2);
  default:
    ASSERTION_VIOLATION;
  }
}

/**
 * Return the result of literal comparison assuming s1 inc t1
 */
Ordering::Result Ordering::compare_s1It1(Result s1_t1, Result s1_t2, Result s2_t1, Result s2_t2) const
{
  ASS_EQ(s1_t1, INCOMPARABLE);

  switch(s2_t2) {
  case GREATER:
    return compare_s1Gt1_s2It2(s1_t1,s1_t2,s2_t1,s2_t2);
  case INCOMPARABLE:
    return compare_s1It1_s2It2(s1_t1,s1_t2,s2_t1,s2_t2);
  case LESS:
    return reverse(compare_s1Gt1_s2It2(s1_t1,s1_t2,s2_t1,s2_t2));
  default:
    ASSERTION_VIOLATION;
  }
}

/**
 * Return the result of literal comparison assuming s1 inc t1 and s2 inc t2
 */
Ordering::Result Ordering::compare_s1It1_s2It2(Result s1_t1, Result s1_t2, Result s2_t1, Result s2_t2) const
{
  ASS_EQ(s1_t1, INCOMPARABLE);
  ASS_EQ(s2_t2, INCOMPARABLE);

  switch(s1_t2) {
  case GREATER:
    return compare_s1Gt1_s1It2_s2It1(s1_t1,s1_t2,s2_t1,s2_t2);
  case INCOMPARABLE:
    return INCOMPARABLE;
  case LESS:
    return reverse(compare_s1Gt1_s1It2_s2It1(s1_t1,s1_t2,s2_t1,s2_t2));
  default:
    ASSERTION_VIOLATION;
  }
}

/**
 * Return the result of literal comparison assuming s1 > t1 and s2 inc t2
 */
Ordering::Result Ordering::compare_s1Gt1_s2It2(Result s1_t1, Result s1_t2, Result s2_t1, Result s2_t2) const
{
  ASS_EQ(s1_t1, GREATER);
  ASS_EQ(s2_t2, INCOMPARABLE);

  switch(s1_t2) {
  case GREATER:
    return GREATER;
  case INCOMPARABLE:
    return INCOMPARABLE;
  case LESS:
    ASS_NEQ(s2_t1, LESS); //would cause s2<t2 by transitivity t2>s1>t1>s2 or t2>=s1>t1>s2
    // ASS_EQ(compare(t1,t2), LESS); //transitivity through s1
    return INCOMPARABLE;
  default:
    ASSERTION_VIOLATION;
  }
}

/**
 * Return the result of literal comparison assuming s1 > t1 and s2 < t2
 */
Ordering::Result Ordering::compare_s1Gt1_s2Lt2(Result s1_t1, Result s1_t2, Result s2_t1, Result s2_t2) const
{
  ASS_EQ(s1_t1, GREATER);
  ASS_EQ(s2_t2, LESS);

  switch(s1_t2) {
  case GREATER:
    // ASS_EQ(compare(s1,s2), GREATER); //transitivity through t2
    return GREATER;
  case INCOMPARABLE:
    return INCOMPARABLE;
  case LESS:
    // ASS_EQ(compare(t1,t2), LESS); //transitivity through t2
    return LESS;
  default:
    ASSERTION_VIOLATION;
  }
}

/**
 * Return the result of literal comparison assuming s1 > t1, s1 inc t2, s2 inc t1
 */
Ordering::Result Ordering::compare_s1Gt1_s1It2_s2It1(Result s1_t1, Result s1_t2, Result s2_t1, Result s2_t2) const
{
  ASS_EQ(s1_t1, GREATER);
  ASS_EQ(s1_t2, INCOMPARABLE);
  ASS_EQ(s2_t1, INCOMPARABLE);

  switch(s2_t2) {
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
