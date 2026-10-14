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
 * @file GoalGuessing.cpp
 * Implements class GoalGuessing.
 */

#include "Lib/Environment.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/SubformulaIterator.hpp"

#include "Shell/SubexpressionIterator.hpp"

#include "GoalGuessing.hpp"

namespace Shell
{

using namespace std;

//////////////////////////
// GoalGuessing
//

void GoalGuessing::apply(Problem& prb)
{
  _lookInside = env.options->guessTheGoal() != Options::GoalGuess::POSITION;
  _checkTop = env.options->guessTheGoal() == Options::GoalGuess::EXISTS_TOP || env.options->guessTheGoal() == Options::GoalGuess::EXISTS_ALL;
  _checkSymbols = env.options->guessTheGoal() == Options::GoalGuess::EXISTS_SYM || env.options->guessTheGoal() == Options::GoalGuess::EXISTS_ALL;
  _checkPosition = env.options->guessTheGoal() == Options::GoalGuess::POSITION;

  if(env.options->guessTheGoal() == Options::GoalGuess::ALL){
    _lookInside=true;
    _checkSymbols=true;
    _checkPosition=true;
  }

  if(_checkSymbols){
    _limit = env.options->gtgLimit();
    countPerUnitUsage(prb.units());
  }

  if(apply(prb.units())) {
    prb.invalidateByRemoval();
  }
}

/**
 * For each function symbol, count the number of units of @c units it occurs in.
 *
 * This statistic used to live in Signature::Symbol as unitUsageCnt and was recomputed
 * as a side effect of Property::scan (which is why preprocess() used to force a rescan
 * right before goal guessing). Goal guessing was its only consumer, and only ever asked
 * about function symbols, so it is computed here and only over the functions.
 */
void GoalGuessing::countPerUnitUsage(UnitList* units)
{
  _perUnitUsageCount.init(env.signature->functions(),0);

  UnitList::Iterator uit(units);
  while(uit.hasNext()) {
    collectFunctors(uit.next());

    DHSet<unsigned, FnvHash, IdentityHash>::Iterator fit(_functorsInUnit);
    while(fit.hasNext()) {
      _perUnitUsageCount[fit.next()]++;
    }
  }
}

/**
 * Collect into _functorsInUnit the function symbols occurring in @c u.
 */
void GoalGuessing::collectFunctors(Unit* u)
{
  _functorsInUnit.reset();

  auto collect = [this](TermList ts) {
    if(ts.isTerm()) {
      Term* t = ts.term();
      if(!t->isSpecial() && !t->isSort()) {
        _functorsInUnit.insert(t->functor());
      }
    }
  };

  if(u->isClause()) {
    Clause* cl = static_cast<Clause*>(u);
    for(unsigned i=0; i<cl->length(); i++) {
      SubtermIterator stit((*cl)[i]);
      while(stit.hasNext()) {
        TermList ts = stit.next();
        // SubtermIterator only follows args(), so it would silently skip whatever
        // hides in the special data of a special term. Clause literals must not
        // contain one: a term with a special subterm cannot be shared.
        ASS(!ts.isTerm() || !ts.term()->isSpecial());
        collect(ts);
      }
    }
  } else {
    // unlike SubtermIterator, this one does descend into special terms
    SubexpressionIterator sei(static_cast<FormulaUnit*>(u)->formula());
    while(sei.hasNext()) {
      SubexpressionIterator::Expression expr = sei.next();
      if(expr.isTerm()) {
        collect(expr.getTerm());
      }
    }
  }
}

bool GoalGuessing::apply(UnitList*& units)
{
  bool modified = false;

  UnitList::Iterator uit(units);
  while(uit.hasNext()) {
    Unit* u = uit.next();

    if(_checkPosition){
      if(u->number() == Unit::getLastParsingNumber()){
        u->inference().setInputType(UnitInputType::NEGATED_CONJECTURE);
        modified=true;
      }
    }

    if(_lookInside){
     if(u->isClause()) {
       Clause* cl = static_cast<Clause*>(u);
       modified |= apply(cl);
     }
     else {
       FormulaUnit* fu = static_cast<FormulaUnit*>(u);
       modified |= apply(fu);
     }
    }
  }
  return modified;
}

bool GoalGuessing::apply(Clause* cl)
{
  if(cl->isPureTheoryDescendant()){ return false; }

  unsigned clen = cl->length();
  for(unsigned i=0; i<clen; i++) {
    if(apply((*cl)[i])){
      cl->inference().setInputType(UnitInputType::NEGATED_CONJECTURE);
      return true;
    }
  }
  return false;
}

bool GoalGuessing::apply(FormulaUnit* fu)
{
  // existential quantification at the top-level is conjecture-like, and so is
  // negated universal quantification (the two are mutually exclusive)
  if(_checkTop && (fu->formula()->connective() == EXISTS ||
      (fu->formula()->connective() == NOT && fu->formula()->uarg()->connective() == FORALL))){
    fu->inference().setInputType(UnitInputType::NEGATED_CONJECTURE);
    return true;
  }

  SubformulaIterator sfit(fu->formula());
  while (sfit.hasNext()) {
    Formula* sf = sfit.next();
    if (sf->connective() == LITERAL && apply(sf->literal())){
      fu->inference().setInputType(UnitInputType::NEGATED_CONJECTURE);
      return true;
    }
  }
  return false;
}

bool GoalGuessing::apply(Literal* lit)
{
  if(!_checkSymbols){ return false; }

     //if(lit->isSpecial()){ return false; }

    // do we care if we have predicate symbols only appearing in the goal?
    //unsigned p = lit->functor();

    TermFunIterator it(lit);
    ASS(it.hasNext());
    it.next(); // to move past the lit symbol
    while(it.hasNext()){
      unsigned f = it.next();
      if(f >= _perUnitUsageCount.size()){ continue; }
      if(_perUnitUsageCount[f] <= _limit){
        //cout << "IDENTIFIED AS GOAL symbol " << env.signature->functionName(f) << endl;
        return true;
      }
    }
    return false;
}

}


