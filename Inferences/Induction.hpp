/*
 * File Induction 
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file Induction.hpp
 * Defines class Induction
 *
 */

#ifndef __Induction__
#define __Induction__

#include <math.h>

#include "Forwards.hpp"

#include "Kernel/TermTransformer.hpp"

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
  LiteralSubsetReplacement(Literal* lit, Term* o, TermList r)
      : _lit(lit), _o(o), _r(r) {
    _occurrences = _lit->countSubtermOccurrences(TermList(_o));
    _maxIterations = pow(2, _occurrences);
  }

  // Returns transformed lit for the first 2^(_occurences) - 1 calls, then returns nullptr.
  // Sets rule to INDUCTION_AXIOM if all occurrences were transformed, otherwise sets rule
  // to GEN_INDUCTION_AXIOM.
  Literal* transformSubset(InferenceRule& rule);

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
  inline OWN_ELEMENT_TYPE next() { 
    Clause* c = _clauses.pop();
    if(env.options->showInduction()){
      env.beginOutput();
      env.out() << "[Induction] generate " << c->toString() << endl; 
      env.endOutput();
    }
    return c; 
  }

private:
  void process(Clause* premise, Literal* lit);

  void produceClauses(Clause* premise, Literal* origLit, Formula* hypothesis, Literal* conclusion, InferenceRule rule);

  void performMathInductionOne(Clause* premise, Literal* origLit, Literal* lit, Term* t, InferenceRule rule); 
  void performMathInductionTwo(Clause* premise, Literal* origLit, Literal* lit, Term* t, InferenceRule rule);

  void performStructInductionOne(Clause* premise, Literal* origLit, Literal* lit, Term* t, InferenceRule rule);
  void performStructInductionTwo(Clause* premise, Literal* origLit, Literal* lit, Term* t, InferenceRule rule);
  void performStructInductionThree(Clause* premise, Literal* origLit, Literal* lit, Term* t, InferenceRule rule);

  void selectInductionScheme(Clause* premise, Literal* origLit, InferenceRule rule);
  void instantiateScheme(Clause* premise, Literal* origLit, InferenceRule rule, InductionScheme* scheme);

  bool notDone(Literal* lit, Term* t);
  Term* getPlaceholderForTerm(Term* t);

  Stack<Clause*> _clauses;
};

};

#endif /*__Induction__*/
