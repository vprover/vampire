/**
 * @file Induction.hpp
 * Defines class Induction
 *
 */

#ifndef __Induction__
#define __Induction__

#include "Forwards.hpp"

#include "Kernel/TermTransformer.hpp"

#include "InferenceEngine.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Saturation;

class ConstantReplacement : public TermTransformer {

public:
  ConstantReplacement(unsigned f, TermList r) : _f(f), _r(r) {} 
  virtual TermList transformSubterm(TermList trm);
private:
  unsigned _f;
  TermList _r;
};

class Induction
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(Induction);
  USE_ALLOCATOR(Induction);

  Induction() {}
  ClauseIterator generateClauses(Clause* premise);

};

class InductionClauseIterator
{
public:
  // all the work happens in the constructor!
  InductionClauseIterator(Clause* premise);

  CLASS_NAME(InductionClauseIterator);
  USE_ALLOCATOR(InductionClauseIterator);
  DECL_ELEMENT_TYPE(Clause*);

  inline bool hasNext() { return _clauses.isNonEmpty(); }
  inline OWN_ELEMENT_TYPE next() { return _clauses.pop(); }

private:
  Stack<Clause*> _clauses;
};

};

#endif /*__Induction__*/
