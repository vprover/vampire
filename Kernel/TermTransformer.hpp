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
  Literal* transform(Literal* lit);
protected:
  virtual TermList transformSubterm(TermList trm) = 0;
};

class TermTransformerTransformTransformed {
public:
  virtual ~TermTransformerTransformTransformed() {}
  Literal* transform(Literal* lit);
protected:
  virtual TermList transformSubterm(TermList trm) = 0;
};


}

#endif // __TermTransformer__
