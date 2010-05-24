/**
 * @file Superposition.hpp
 * Defines class Superposition.
 */


#ifndef __Superposition__
#define __Superposition__

#include "Forwards.hpp"
#include "Indexing/TermIndex.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class Superposition
: public GeneratingInferenceEngine
{
public:
  void attach(SaturationAlgorithm* salg);
  void detach();

  ClauseIterator generateClauses(Clause* premise);


private:
  static Clause* performSuperposition(
	  Clause* rwClause, Literal* rwLiteral, TermList rwTerm,
	  Clause* eqClause, Literal* eqLiteral, TermList eqLHS,
	  ResultSubstitutionSP subst, bool eqIsResult, Limits* limits);

  struct ForwardResultFn;
  struct RewriteableSubtermsFn;
  struct ApplicableRewritesFn;

  struct LHSsFn;
  struct RewritableResultsFn;
  struct BackwardResultFn;

  SuperpositionSubtermIndex* _subtermIndex;
  SuperpositionLHSIndex* _lhsIndex;
};


};

#endif /* __Superposition__ */
