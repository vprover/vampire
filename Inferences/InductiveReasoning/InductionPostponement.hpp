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
 * @file InductionPostponement.hpp
 * Defines class InductionPostponement
 *
 */

#ifndef __InductionPostponement__
#define __InductionPostponement__

#include "Forwards.hpp"

#include "Indexing/InductionFormulaIndex.hpp"
#include "Indexing/TermSubstitutionTree.hpp"
#include "Indexing/LiteralSubstitutionTree.hpp"

namespace Inferences
{

struct InductionContext;
class InductionClauseIterator;

namespace InductiveReasoning
{

class InductionPostponement
{
public:
  InductionPostponement(InductionFormulaIndex& formulaIndex)
      : _salg(nullptr), _formulaIndex(formulaIndex), _postponedTermIndex(), _postponedLitIndex(),
        _lhsIndex(nullptr), _literalIndex(nullptr) {}

  void attach(SaturationAlgorithm* salg);
  void detach();

  void checkForPostponedInductions(Literal* lit, Clause* cl, InductionClauseIterator& clIt);
  bool maybePostpone(const InductionContext& ctx, InductionFormulaIndex::Entry* e);

private:
  void performInductionsIfNeeded(TermList t, Literal* lit, Clause* cl, InductionClauseIterator& clIt);
  Clause* findActivatingClauseForIndex(const InductionContext& ctx, unsigned index);

  SaturationAlgorithm* _salg;
  InductionFormulaIndex& _formulaIndex;
  TermSubstitutionTree _postponedTermIndex;
  LiteralSubstitutionTree _postponedLitIndex;
  TermIndex* _lhsIndex;
  LiteralIndex* _literalIndex;
  DHMap<Literal*,Stack<InductionFormulaKey>> _literalMap;
  DHSet<Literal*> _toBeRemoved;
  bool _enabled = false;
};

}

}

#endif /*__InductionPostponement__*/
