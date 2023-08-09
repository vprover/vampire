/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
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
  CLASS_NAME(Superposition);
  USE_ALLOCATOR(Superposition);

  void attach(SaturationAlgorithm* salg);
  void detach();

  ClauseIterator generateClauses(Clause* premise);

  static bool checkForLeftmostInnermostReducibleTerm(TermList sideS, TermList rwTermS, const Ordering& ordering, DemodulationLHSIndex* lhsIndex);
  static bool checkForLeftmostInnermostReducibleTerm(Clause* eqClause, Clause* rwClause, Term* rwTermS, ResultSubstitution* subst, bool eqIsResult, const Ordering& ordering, DemodulationLHSIndex* lhsIndex);
  static bool checkForSmallerReducibleTerm(Clause* eqClause, Clause* rwClause, TermList rwTermS, ResultSubstitution* subst, bool eqIsResult, const Ordering& ordering, DemodulationLHSIndex* lhsIndex);
  static bool checkTermReducible(Term* t, const Ordering& ordering, DemodulationLHSIndex* lhsIndex);

private:
  Clause* performSuperposition(
    Clause* rwClause, Literal* rwLiteral, TermList rwTerm,
    Clause* eqClause, Literal* eqLiteral, TermList eqLHS,
    ResultSubstitutionSP subst, bool eqIsResult, PassiveClauseContainer* passiveClauseContainer,
          UnificationConstraintStackSP constraints);

  bool checkClauseColorCompatibility(Clause* eqClause, Clause* rwClause);
  static bool earlyWeightLimitCheck(Clause* eqClause, Literal* eqLit,
      Clause* rwClause, Literal* rwLit, TermList rwTerm, TermList eqLHS, TermList eqRHS,
      ResultSubstitutionSP subst, bool eqIsResult, PassiveClauseContainer* passiveClauseContainer, unsigned numPositiveLiteralsLowerBound, const Inference& inf);

  static bool checkSuperpositionFromVariable(Clause* eqClause, Literal* eqLit, TermList eqLHS);

  struct ForwardResultFn;

  struct LHSsFn;
  struct RewritableResultsFn;
  struct BackwardResultFn;

  SuperpositionSubtermIndex* _subtermIndex;
  SuperpositionLHSIndex* _lhsIndex;
  DemodulationLHSIndex* _demLhsIndex;
};


};

#endif /* __Superposition__ */
