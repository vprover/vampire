
/*
 * File GoalGuessing.cpp.
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
    if(u->isClause()) {
      Clause* cl = static_cast<Clause*>(u);
      modified |= apply(cl);
    }
    else {
      FormulaUnit* fu = static_cast<FormulaUnit*>(u);
      modified |= apply(fu);
    }
  }
  return modified;
}

bool GoalGuessing::apply(Clause* cl)
{
  CALL("GoalGuessing::apply(Clause* cl)");

  unsigned clen = cl->length();
  bool looksLikeGoal = false;
  for(unsigned i=0; i<clen; i++) {
    Literal* lit = (*cl)[i];
    looksLikeGoal |= apply(lit); // need to consider all as apply(Lit) may update signature
  }
  if(looksLikeGoal){ cl->setInputType(Unit::NEGATED_CONJECTURE); }
  return looksLikeGoal; 
}
bool GoalGuessing::apply(FormulaUnit* fu)
{
  CALL("GoalGuessing::apply(FormulaUnit* fu)");

  bool looksLikeGoal = false;

  // existential quantification at the top-level is conjecture-like
  if(fu->formula()->connective() == EXISTS){
    looksLikeGoal = true;
  }

  SubformulaIterator sfit(fu->formula());
  while (sfit.hasNext()) {
    Formula* sf = sfit.next();
    if (sf->connective() == LITERAL){
      looksLikeGoal |= apply(sf->literal()); // need to consider all as apply(Lit) may update signature
    }
  }
  if(looksLikeGoal){ fu->setInputType(Unit::NEGATED_CONJECTURE); }
  return looksLikeGoal;
}

bool GoalGuessing::apply(Literal* lit)
{
  CALL("GoalGuessing::apply(Literal* lit)");

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
      if(unitUsageCnt == 1){
        //cout << "IDENTIFIED AS GOAL symbol " << env.signature->functionName(f) << endl;
        env.signature->getFunction(f)->markInGoal();
        found = true;
      }
    }
    return found;
}

}


