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
 * @file Induction.hpp
 * Defines class Induction
 *
 */

#ifndef __Induction__
#define __Induction__

#include <cmath>

#include "Forwards.hpp"

#include "Indexing/LiteralIndex.hpp"
#include "Indexing/TermIndex.hpp"

#include "Kernel/TermTransformer.hpp"
#include "Kernel/Theory.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/List.hpp"

#include "InductionHelper.hpp"
#include "InferenceEngine.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Saturation;

class TermReplacement : public TermTransformer {

public:
  TermReplacement(Term* o, TermList r) : _o(o), _r(r) {} 
  virtual TermList transformSubterm(TermList trm);
private:
  Term* _o;
  TermList _r;
};

class LiteralSubsetReplacement : TermTransformer {
public:
  LiteralSubsetReplacement(Literal* lit, Term* o, TermList r, const unsigned maxSubsetSize)
      : _lit(lit), _o(o), _r(r), _maxSubsetSize(maxSubsetSize) {
    _occurrences = _lit->countSubtermOccurrences(TermList(_o));
    _maxIterations = pow(2, _occurrences);
  }

  // Returns transformed lit for the first 2^(_occurences) - 1 calls, then returns nullptr.
  // Sets rule to INDUCTION_AXIOM if all occurrences were transformed, otherwise sets rule
  // to GEN_INDUCTION_AXIOM.
  Literal* transformSubset(InferenceRule& rule);

  List<pair<Literal*, InferenceRule>>* getListOfTransformedLiterals(InferenceRule rule);

protected:
  virtual TermList transformSubterm(TermList trm);

private:
  // _iteration serves as a map of occurrences to replace
  unsigned _iteration = 0;
  unsigned _maxIterations;
  // Counts how many occurrences were already encountered in one transformation
  unsigned _matchCount = 0;
  unsigned _occurrences;
  const unsigned _maxOccurrences = 20;
  Literal* _lit;
  Term* _o;
  TermList _r;
  const unsigned _maxSubsetSize;
};

class Induction
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(Induction);
  USE_ALLOCATOR(Induction);

  Induction() {}

  void attach(SaturationAlgorithm* salg) override;
  void detach() override;

  ClauseIterator generateClauses(Clause* premise) override;

#if VDEBUG
  void setTestIndices(const Stack<Index*>& indices) override {
    _comparisonIndex = static_cast<LiteralIndex*>(indices[0]);
  }
#endif // VDEBUG

private:
  // The following pointers can be null if int induction is off.
  LiteralIndex* _comparisonIndex = nullptr;
  TermIndex* _inductionTermIndex = nullptr;
};

class InductionClauseIterator
{
public:
  // all the work happens in the constructor!
  InductionClauseIterator(Clause* premise, InductionHelper helper, const Options& opt)
      : _helper(helper), _opt(opt)
  {
    processClause(premise);
  }

  CLASS_NAME(InductionClauseIterator);
  USE_ALLOCATOR(InductionClauseIterator);
  DECL_ELEMENT_TYPE(Clause*);

  inline bool hasNext() { return _clauses.isNonEmpty(); }
  inline OWN_ELEMENT_TYPE next() { 
    Clause* c = _clauses.pop();
    if(_opt.showInduction()){
      env.beginOutput();
      env.out() << "[Induction] generate " << c->toString() << endl; 
      env.endOutput();
    }
    return c; 
  }

private:
  void processClause(Clause* premise);
  void processLiteral(Clause* premise, Literal* lit);
  void processIntegerComparison(Clause* premise, Literal* lit);

  // Clausifies the hypothesis, resolves it against the conclusion/toResolve,
  // and increments relevant statistics.
  void produceClauses(Clause* premise, Literal* origLit, Formula* hypothesis, InferenceRule rule, const pair<Literal*, SLQueryResult>& conclusion);
  void produceClauses(Clause* premise, Literal* origLit, Formula* hypothesis, InferenceRule rule, const List<pair<Literal*, SLQueryResult>>* bounds);

  // Calls generalizeAndPerformIntInduction(...) for those induction literals from inductionTQRsIt,
  // which are non-redundant with respect to the indTerm, bounds, and increasingness.
  // Note: indTerm is passed to avoid recomputation.
  void performIntInductionOnEligibleLiterals(Term* origTerm, Term* indTerm, TermQueryResultIterator inductionTQRsIt, bool increasing, TermQueryResult bound1, DHMap<Term*, TermQueryResult>& bounds2);
  // Calls generalizeAndPerformIntInduction(...) for those bounds from lowerBound, upperBound
  // (and the default bound) which are non-redundant with respect to the origLit, origTerm,
  // and increasingness.
  // Note: indLits and indTerm are passed to avoid recomputation.
  void performIntInductionForEligibleBounds(Clause* premise, Literal* origLit, Term* origTerm, List<pair<Literal*, InferenceRule>>*& indLits, Term* indTerm, bool increasing, DHMap<Term*, TermQueryResult>& bounds1, DHMap<Term*, TermQueryResult>& bounds2);
  // If indLits is empty, first fills it with either generalized origLit, or just by origLit itself
  // (depending on whether -indgen is on).
  // Then, performs int induction for each induction literal from indLits using bound1
  // (and optionalBound2 if provided) as bounds.
  // Note: indLits may be created in this method, but it needs to be destroyed outside of it.
  void generalizeAndPerformIntInduction(Clause* premise, Literal* origLit, Term* origTerm, List<pair<Literal*, InferenceRule>>*& indLits, Term* indTerm, bool increasing, TermQueryResult& bound1, TermQueryResult* optionalBound2);

  void performIntInduction(Clause* premise, Literal* origLit, Literal* lit, Term* t, InferenceRule rule, bool increasing, const TermQueryResult& bound1, TermQueryResult* optionalBound2);

  void performStructInductionOne(Clause* premise, Literal* origLit, Literal* lit, Term* t, InferenceRule rule);
  void performStructInductionTwo(Clause* premise, Literal* origLit, Literal* lit, Term* t, InferenceRule rule);
  void performStructInductionThree(Clause* premise, Literal* origLit, Literal* lit, Term* t, InferenceRule rule);

  bool notDone(Literal* lit, Term* t);
  bool notDoneInt(Literal* lit, Term* t, bool increasing, Term* bound1, Term* optionalBound2, bool fromComparison);
  Term* getPlaceholderForTerm(Term* t);

  Stack<Clause*> _clauses;
  InductionHelper _helper;
  const Options& _opt;
};

};

#endif /*__Induction__*/
