
/*
 * File BetaReductionEngine.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file BetaReductionEngine.hpp
 * carries out beta-reduction
 * @since 01/04/2018 Manchester
 */

#ifndef __BetaReductionEngine__
#define __BetaReductionEngine__

#include "Kernel/Formula.hpp"
#include "Kernel/Unit.hpp"

using namespace Kernel;

namespace Shell {

/**
 * Class implementing beta-reduction.
 * @since 05/04/2018
 */
class BetaReductionEngine
{
public:
  BetaReductionEngine ();
  Term* BetaReduce(Term* abstractedTerm, TermList redax);
private:
  static TermList lift(TermList tl, unsigned value, unsigned cutoff);
  bool areEqual(vstring indexName, unsigned replace);
  vstring decIndex(vstring index);  

}; // class BetaReductionEngine

}

#endif
