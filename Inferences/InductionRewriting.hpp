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
 * @file InductionRewriting.hpp
 * Defines class InductionRewriting
 *
 */

#ifndef __InductionRewriting__
#define __InductionRewriting__

#include "Forwards.hpp"

#include "InferenceEngine.hpp"
#include "Induction.hpp"

#include "Kernel/EqHelper.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/TermTransformer.hpp"

#include "Lib/ScopedPtr.hpp"
#include "Lib/SharedSet.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class SingleOccurrenceReplacementIterator : public IteratorCore<Term*> {
public:
  CLASS_NAME(SingleOccurrenceReplacementIterator);
  USE_ALLOCATOR(SingleOccurrenceReplacementIterator);
  SingleOccurrenceReplacementIterator(Term* t, Term* o, TermList r)
      : _t(t), _o(o), _r(r), _occurrences(_t == _o ? 1 : _t->countSubtermOccurrences(TermList(_o))) {}

  bool hasNext() override {
    return _iteration < _occurrences;
  }
  Term* next() override;

private:
  unsigned _iteration = 0;
  Term* _t;
  Term* _o;
  TermList _r;
  unsigned _occurrences;

  class Replacer : public TermTransformer {
  public:
    Replacer(Term* o, TermList r, unsigned i)
      : _o(o), _r(r), _i(i), _matchCount(0) {}

  private:
    TermList transformSubterm(TermList trm) override;

    Term* _o;
    TermList _r;
    unsigned _i;
    unsigned _matchCount;
  };
};

TermList replaceOccurrence(Term* t, Term* orig, TermList repl, const Position& pos);
vstring posToString(const Position& pos);
Term* getTermAtPos(Term* t, const Position& p);
bool isInductionTerm(Term* t);
void getTermsToInductOn(Literal* lit, const Stack<pair<Position,bool>>& ps, DHSet<Term*>& indTerms);
Position getRightmostPosition(const Stack<pair<Position,bool>>& ps, bool left);
bool toTheLeft(const Position& p1, const Position& p2);
bool hasTermToInductOn(Term* t);
VirtualIterator<pair<Term*,Position>> getPositions(TermList t, Term* st);
bool linear(Term* t);
bool shouldChain(Term* lhs);
VirtualIterator<TypedTermList> lhsIterator(Literal* lit);

class PositionalNonVariableNonTypeIterator
  : public IteratorCore<pair<Term*,Position>>
{
public:
  PositionalNonVariableNonTypeIterator(const PositionalNonVariableNonTypeIterator&);

  PositionalNonVariableNonTypeIterator(Term* term) : _stack(8)
  {
    _stack.push(make_pair(term,Position()));
  }

  /** true if there exists at least one subterm */
  bool hasNext() { return !_stack.isEmpty(); }
  pair<Term*,Position> next();
private:
  /** available non-variable subterms */
  Stack<pair<Term*,Position>> _stack;
}; // PositionalNonVariableNonTypeIterator

class InductionRewriting
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(InductionRewriting);
  USE_ALLOCATOR(InductionRewriting);

  InductionRewriting(Induction* induction)
    : _lhsIndex(0), _induction(induction) {}

  void attach(SaturationAlgorithm* salg) override;
  void detach() override;
  ClauseIterator generateClauses(Clause* premise) override;

private:
  Clause* perform(Clause* rwClause, Literal* rwLit, Term* rwSide, Term* rwTerm, const Position& pos,
    Clause* eqClause, Literal* eqLit, TermList eqLhs, ResultSubstitution* subst, bool eqIsResult);

  // void exploreTerm(Term* t, bool left);
  void exploreTermLMIM(Term* t, bool left);

  TermIndex* _lhsIndex;
  TermIndex* _subtermIndex;
  Induction* _induction;

  DHMap<Term*,Stack<Position>> _leftTerms;
  DHMap<Term*,Stack<Position>> _rightTerms;
};

}

#endif /*__InductionRewriting__*/