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
#include "Kernel/TermIterators.hpp"
#include "Kernel/SubformulaIterator.hpp"

#include "Property.hpp"

#include "GoalGuessing.hpp"

namespace Shell
{

//////////////////////////
// GoalGuessing
//

void GoalGuessing::apply(Problem& prb)
{
  CALL("GoalGuessing::apply(Problem&)");

  _lookInside = env.options->guessTheGoal() != Options::GoalGuess::POSITION;
  _checkTop = env.options->guessTheGoal() == Options::GoalGuess::EXISTS_TOP || env.options->guessTheGoal() == Options::GoalGuess::EXISTS_ALL;
  _checkSymbols = env.options->guessTheGoal() == Options::GoalGuess::EXISTS_SYM || env.options->guessTheGoal() == Options::GoalGuess::EXISTS_ALL;
  _checkPosition = env.options->guessTheGoal() == Options::GoalGuess::POSITION;

  if(env.options->guessTheGoal() == Options::GoalGuess::ALL){
    _lookInside=true;
    _checkSymbols=true;
    _checkPosition=true;
  }

  if(apply(prb.units())) {
    prb.invalidateByRemoval();
  }
}

bool GoalGuessing::apply(UnitList*& units)
{
  CALL("GoalGuessing::apply(UnitList*& units)");

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
  CALL("GoalGuessing::apply(Clause* cl)");

  if(cl->isPureTheoryDescendant()){ return false; }

  unsigned clen = cl->length();
  bool looksLikeGoal = false;
  for(unsigned i=0; i<clen; i++) {
    Literal* lit = (*cl)[i];
    looksLikeGoal |= apply(lit); // need to consider all as apply(Lit) may update signature
  }
  if(looksLikeGoal){ cl->inference().setInputType(UnitInputType::NEGATED_CONJECTURE); }
  return looksLikeGoal; 
}
bool GoalGuessing::apply(FormulaUnit* fu)
{
  CALL("GoalGuessing::apply(FormulaUnit* fu)");

  bool looksLikeGoal = false;

  // existential quantification at the top-level is conjecture-like
  if(_checkTop && fu->formula()->connective() == EXISTS){
    looksLikeGoal = true;
  }
  // negated universal quantification at the top level is conjecture-like
  if(_checkTop && fu->formula()->connective() == NOT && fu->formula()->uarg()->connective() == FORALL){
    looksLikeGoal = true;
  }

  SubformulaIterator sfit(fu->formula());
  while (sfit.hasNext()) {
    Formula* sf = sfit.next();
    if (sf->connective() == LITERAL){
      looksLikeGoal |= apply(sf->literal()); // need to consider all as apply(Lit) may update signature
    }
  }
  if(looksLikeGoal){ fu->inference().setInputType(UnitInputType::NEGATED_CONJECTURE); }
  return looksLikeGoal;
}

bool GoalGuessing::apply(Literal* lit)
{
  CALL("GoalGuessing::apply(Literal* lit)");

  if(!_checkSymbols){ return false; }

     //if(lit->isSpecial()){ return false; }

    // do we care if we have predicate symbols only appearing in the goal?
    //unsigned p = lit->functor();
    bool found = false;

    TermFunIterator it(lit);
    ASS(it.hasNext());
    it.next(); // to move past the lit symbol 
    while(it.hasNext()){
      unsigned f = it.next();
      if(f > env.signature->functions()){ continue; }
      unsigned unitUsageCnt = env.signature->getFunction(f)->unitUsageCnt();
      static unsigned unitUsageCntLimit = env.options->gtgLimit();
      if(unitUsageCnt <= unitUsageCntLimit){
        //cout << "IDENTIFIED AS GOAL symbol " << env.signature->functionName(f) << endl;
        env.signature->getFunction(f)->markInGoal();
        found = true;
      }
    }
    return found;
}

}


