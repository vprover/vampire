/*
 * File CustomKBO.hpp.
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
 * @file CustomKBO.hpp
 * Defines class CustomKBO for instances of the Knuth-Bendix ordering with custom weights and precedence
 *
 * @since 30/04/2008 flight Brussels-Tel Aviv
 */

#ifndef __CustomKBO__
#define __CustomKBO__

#include "Lib/STL.hpp"
#include "Ordering.hpp"

namespace Kernel {

using namespace Lib;

/**
 * Class for instances of the Knuth-Bendix orderings
 * @since 30/04/2008 flight Brussels-Tel Aviv
 */
class CustomKBO
: public PrecedenceOrdering
{
public:
  CLASS_NAME(CustomKBO);
  USE_ALLOCATOR(CustomKBO);

  CustomKBO(Problem& prb, const Options& opt);
  virtual ~CustomKBO();

  using PrecedenceOrdering::compare;
  Result compare(TermList tl1, TermList tl2) const override;
protected:
  Result comparePredicates(Literal* l1, Literal* l2) const override;

  class State;
  /** Weight of variables */
  int _variableWeight;
  /** Weight of function symbols specified with option --custom_kbo_weights */
  vvector<int> _symbolWeights;
  /** Weight of function symbols for which no weight has been specified */
  int _defaultSymbolWeight;

  int functionSymbolWeight(unsigned fun) const;

  bool allConstantsHeavierThanVariables() const { return false; }
  bool existsZeroWeightUnaryFunction() const { return false; }


  /**
   * State used for comparing terms and literals
   */
  mutable State* _state;
};

}
#endif
