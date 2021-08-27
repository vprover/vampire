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
 * @file Induction.cpp
 * Implements class Induction.
 */

#include "Indexing/Index.hpp"
#include "Indexing/ResultSubstitution.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Sorts.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Theory.hpp"

#include "Shell/Options.hpp"

#include "RapidHelper.hpp"

namespace Kernel {


bool RapidHelper::isIntegerComparisonLiteral(Literal* lit) {
  CALL("RapidHelper::isIntegerComparisonLiteral");

  if (!theory->isInterpretedPredicate(lit)) return false;
  switch (theory->interpretPredicate(lit)) {
    case Theory::INT_LESS:
      // The only supported integer comparison predicate is INT_LESS.
      break;
    case Theory::INT_LESS_EQUAL:
    case Theory::INT_GREATER_EQUAL:
    case Theory::INT_GREATER:
      // All formulas should be normalized to only use INT_LESS and not other integer comparison predicates.
      ASSERTION_VIOLATION;
    default:
      // Not an integer comparison.
      return false;
  }
  return true;
}

bool RapidHelper::isDensityLiteral(Literal* l, unsigned& varFunctor, unsigned& tpFunctor)
{
  CALL("RapidHelper::isDensityLiteral");

  if(l->arity()){
    return false;
  }

  vstring name = env.signature->getPredicate(l->functor())->name();
  if(name.find("Dense") == vstring::npos){
    return false;
  }

  unsigned posOfFirstDash = 6;
  unsigned posOfSecondDash = name.find('-', 7);
 
  vstring programVarName = name.substr(posOfFirstDash + 1, posOfSecondDash - posOfFirstDash - 1);
  vstring timePoint = name.substr(posOfSecondDash + 1, name.length() - posOfSecondDash - 2);

  varFunctor = env.signature->getFunctionNumber(programVarName, 1);
  //very dangerous! the timepoint cna take multiple loop counters, so may
  //not have arity 1!
  tpFunctor = env.signature->getFunctionNumber(timePoint, 1);
  return true;
}

bool RapidHelper::isRightLimitLiteral(Literal* l) {
  CALL("RapidHelper::isLimitLiteral");

  //only interested in <
  if(!isIntegerComparisonLiteral(l) || !l->polarity()){
    return false;
  }

  TermList rhs = *l->nthArgument(1);
  if(rhs.isVar()){
    return false;
  }

  Term* t = rhs.term();
  if(t->arity() != 1){
    return false;
  }

  TermList timePoint = *t->nthArgument(0);
  if(timePoint.isVar()){
    return false;
  }

  Term* tp = timePoint.term();
  unsigned f = tp->functor();
  if(!env.signature->getFunction(f)->timePoint()){
    //not actually a timepoint
    return false;
  }

  if(tp->arity() != 1){
    //either of the form l# or of the form l(nl#, nl#,...)
    //for now we ignore the nested loop case
    return false;
  }

  TermList lastLoopCount = *tp->nthArgument(0);
 
  if(lastLoopCount.isVar()){
    return false;
  }

  f = lastLoopCount.term()->functor();
  if(!env.signature->getFunction(f)->finalLoopCount()){
    return false;
  }

  return true;
}

bool RapidHelper::isLeftLimitLiteral(Literal* l) {
  CALL("RapidHelper::isLimitLiteral");

  //only interested in >=
  if(!isIntegerComparisonLiteral(l) || l->polarity()){
    return false;
  }

  TermList rhs = *l->nthArgument(1);
  if(rhs.isVar()){
    return false;
  }

  Term* t = rhs.term();

  if(env.signature->getFunction(t->functor())->integerConstant()){
    return true;
  }

  if(t->arity() != 1){
    return false;
  }

  TermList timePoint = *t->nthArgument(0);
  if(timePoint.isVar()){
    return false;
  }

  Term* tp = timePoint.term();
  unsigned f = tp->functor();
  if(!env.signature->getFunction(f)->timePoint()){
    //not actually a timepoint
    return false;
  }

  if(tp->arity() != 1){
    //either of the form l# or of the form l(nl#, nl#,...)
    //for now we ignore the nested loop case
    return false;
  }

  TermList zero = *tp->nthArgument(0);
 
  if(zero.isVar()){
    return false;
  }

  //TODO update to the non-nat case 
  auto natTA = env.signature->getNat();
  if(natTA){
    if(zero != natTA->createZero()){
      return false;
    }
  }

  return true;
}

bool RapidHelper::isFinalLoopCount(TermList t)
{
  CALL("RapidHelper::isFinalLoopCount");

  if(!t.isTerm()) return false;
  return env.signature->getFunction(t.term()->functor())->finalLoopCount();
}


}  // namespace Inferences
