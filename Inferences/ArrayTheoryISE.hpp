/**
 * @file ArrayTheoryISE.hpp
 * Defines class ArrayTheoryISE.
 *
 * The "extensionality resolution project" initially started out to improve
 * Vampire's reasoning in the theory of arrays. A first attempt was to add some
 * simple rewrite rules. However, the code here is not used at the moment.
 *
 * Adding this rewrite rules might be useful, but then the code has to be
 * revised. For example, applying rewrite rules exhaustively is implemented very
 * inefficiently.
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
  unsigned _select2Functor;
  unsigned _store1Functor;
  unsigned _store2Functor;
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
