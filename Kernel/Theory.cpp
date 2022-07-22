/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Theory.hpp"
#if WITH_GMP
#include "Theory_gmp.cpp"
#else
#include "Theory_int.cpp"
#endif


/**
 * Return true iff @b t is an interpreted function interpreted
 * as @b itp
 */
bool Theory::isInterpretedFunction(unsigned f, Interpretation itp)
{
  CALL("Theory::isInterpretedFunction(unsigned,Interpretation)");
  return isInterpretedFunction(f) && interpretFunction(f)==itp;
}
/**
 * Return true iff @b t is an interpreted function interpreted
 * as @b itp
 */
bool Theory::isInterpretedFunction(Term* t, Interpretation itp)
{
  CALL("Theory::isInterpretedFunction(Term*,Interpretation)");

  return isInterpretedFunction(t->functor(), itp);
}

/**
 * Return true iff @b t is an interpreted function interpreted
 * as @b itp
 */
bool Theory::isInterpretedFunction(TermList t, Interpretation itp)
{
  CALL("Theory::isInterpretedFunction(TermList,Interpretation)");
  return t.isTerm() && isInterpretedFunction(t.term(), itp);
}
