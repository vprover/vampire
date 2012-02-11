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
  Clause* performSuperposition(
	  Clause* rwClause, Literal* rwLiteral, TermList rwTerm,
	  Clause* eqClause, Literal* eqLiteral, TermList eqLHS,
	  ResultSubstitutionSP subst, bool eqIsResult, Limits* limits);

  bool checkClauseColorCompatibility(Clause* eqClause, Clause* rwClause);
  static int getWeightLimit(Clause* eqClause, Clause* rwClause, Limits* limits);
  static bool earlyWeightLimitCheck(Clause* eqClause, Literal* eqLit,
      Clause* rwClause, Literal* rwLit, TermList eqLHS, TermList eqRHS, int weightLimit,
      int& nonInvolvedLiteralWLB);
  static bool checkWeightLimitAfterSubst(int nonInvolvedLiteralWLB, Literal* rwLit,
      TermList rwTerm, TermList eqLHSSubst, TermList eqRHSSubst, int weightLimit);
  static bool checkWeightLimitAfterRWSubst(int nonInvolvedLiteralWLB, Literal* rwLitS,
      TermList eqLHSSubst, TermList eqRHSSubst, int weightLimit);

  static bool checkSuperpositionFromVariable(Clause* eqClause, Literal* eqLit, TermList eqLHS);

  static size_t getSubtermOccurrenceCount(Term* trm, TermList subterm);

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
