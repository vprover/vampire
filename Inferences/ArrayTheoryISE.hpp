/**
 * @file ArrayTheoryISE.hpp
 * Defines class ArrayTheoryISE.
 */

#ifndef __ArrayTheoryISE__
#define __ArrayTheoryISE__

#include "Forwards.hpp"
#include "Inferences/InferenceEngine.hpp"
#include "Kernel/TermTransformer.hpp"

namespace Inferences {

class ArrayTermTransformer
  :  public TermTransformer
{
public:
  ArrayTermTransformer();
  ~ArrayTermTransformer();
  Literal* rewriteNegEqByExtensionality(Literal* l);
protected:
  TermList transformSubterm(TermList trm);
private:
  unsigned _select1Functor;
  unsigned _store1Functor;
  unsigned _array1Sort;
  unsigned _intSort;
  unsigned _array1SkolemFunction;
};

class ArrayTheoryISE
  : public ImmediateSimplificationEngine
{
public:
  ArrayTheoryISE();
  Clause* simplify(Clause* cl);
private:
  ArrayTermTransformer _transformer;
};

};

#endif /* __ArrayTheoryISE__ */
