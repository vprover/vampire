
/*
 * File TermTransformer.hpp.
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
 * @file TermTransformer.hpp
 * Defines class TermTransformer.
 */

#ifndef __TermTransformer__
#define __TermTransformer__

#include "Forwards.hpp"



namespace Kernel {

/**
 * Class to allow for easy transformations of subterms in shared literals.
 *
 * The inheriting class implemets function transform(TermList)
 * and then the function transform(Literal*) uses it to transform subterms
 * of the given literal.
 *
 * The literal and subterms returned by the transform(TermList) function have
 * to be shared.
 */
class TermTransformer {
public:
  virtual ~TermTransformer() {}
  Term* transform(Term* term);
  Literal* transform(Literal* lit);
protected:
  virtual TermList transformSubterm(TermList trm) = 0;
  Term* transformSpecial(Term* specialTerm);
  TermList transform(TermList ts);
  Formula* transform(Formula* f);
};

/**
 * TODO: WTF the name?
 *   --> rename to SumbtermEvaluator?
 */
class TermTransformerTransformTransformed {
public:
  virtual ~TermTransformerTransformTransformed() {}
  Term* transform(Term* term);
  Literal* transform(Literal* lit);
protected:
  virtual TermList transformSubterm(TermList trm) = 0;
  /**
   * TODO: these functions are exactly the same as in TermTransformer, code duplication must be removed!
   */
  TermList transform(TermList ts);
  Formula* transform(Formula* f);
};


}

#endif // __TermTransformer__
