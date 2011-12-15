/**
 * @file HornRevealer.cpp
 * Implements class HornRevealer.
 */

#include "Lib/Environment.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/LiteralSelector.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"

#include "Statistics.hpp"

#include "HornRevealer.hpp"

#undef LOGGING
#define LOGGING 0

namespace Shell
{

void HornRevealer::apply(Problem& prb)
{
  CALL("HornRevealer::apply(Problem&)");

  //TODO: move the information on swapping predicate polarity for Horn into the Problem

  apply(prb.units());
}

void HornRevealer::apply(UnitList*& units)
{
  CALL("HornRevealer::apply");

  buildSatProblem(units);

  _solver.ensureVarCnt(env.signature->predicates()+1);
  _solver.addClauses(pvi( SATClauseStack::Iterator(_satPrb) ), false);

  if(_solver.getStatus()==SATSolver::SATISFIABLE) {
    LOG("pp_hr","Horn discovered");
    discoverGoals(units);

    unsigned preds = env.signature->predicates();
    for(unsigned i=0; i<preds; i++) {
      bool reversed = isReversed(i);
      if(reversed) {
	LOG("pp_hr","reversed: " << env.signature->predicateName(i));
	LiteralSelector::reversePredicatePolarity(i, true);
	env.statistics->hornReversedPredicates++;
      }
    }
  }
}

void HornRevealer::discoverGoals(UnitList*& units)
{
  CALL("HornRevealer::discoverGoals");

  UnitList::DelIterator uit(units);
  while(uit.hasNext()) {
    Clause* cl = static_cast<Clause*>(uit.next());
    ASS(cl->isClause());
    bool markedAsGoal = cl->inputType()!=Unit::AXIOM;
    bool shouldBeGoal = isGoal(cl);
    if(markedAsGoal==shouldBeGoal) {
      continue;
    }

    Inference* inf = new Inference1(Inference::REORDER_LITERALS, cl);
    Unit::InputType inpType = shouldBeGoal ? Unit::CONJECTURE : Unit::AXIOM;
    Clause* newCl = Clause::fromIterator(Clause::Iterator(*cl), inpType, inf);
    uit.replace(newCl);
    LOG("pp_hr","Horn revealer changed inp type: " << inpType <<"\n  "<< newCl->toString());
  }
}

bool HornRevealer::isReversed(unsigned pred)
{
  CALL("HornRevealer::isReversed");
  ASS_EQ(_solver.getStatus(),SATSolver::SATISFIABLE);

  //if prop variable is true, we don't reverse the predicate
  return !_solver.getAssignment(pred2var(pred)).isFalse();
}

bool HornRevealer::isGoal(Clause* cl)
{
  CALL("HornRevealer::isGoal");

//  LOG("isGoal:\n"<<cl->toString());
  bool hasPositive = false;

  Clause::Iterator cit(*cl);
  while(cit.hasNext()) {
    Literal* l = cit.next();
    unsigned pred = l->functor();
    bool polarity = l->isPositive();

    bool posPolarity = !isReversed(pred);

    if(polarity==posPolarity) {
//      LOG("pos:"<<l->toString());
      ASS_REP(!hasPositive, cl->toString());
      hasPositive = true;
    }
  }
  return !hasPositive;
}

void HornRevealer::buildSatProblem(UnitList* units)
{
  CALL("HornRevealer::buildSatProblem");
  ASS(_satPrb.isEmpty());

  //we ensure that the polarity of equality doesn't change
  static SATLiteralStack slits;
  slits.reset();
  slits.push(SATLiteral(pred2var(0), true));
  SATClause* scl = SATClause::fromStack(slits);
  _satPrb.push(scl);

  UnitList::Iterator uit(units);
  while(uit.hasNext()) {
    Clause* cl = static_cast<Clause*>(uit.next());
    ASS(cl->isClause());
    addToSatProblem(cl);
  }
}

void HornRevealer::addToSatProblem(Clause* cl)
{
  CALL("HornRevealer::addToSatProblem");
//  LOG(cl->toString());

  static SATLiteralStack slits;

  unsigned hlen = cl->length();
  for(unsigned i=0; i<hlen; i++) {
    Literal* iLit = (*cl)[i];
    unsigned iPred = iLit->functor();
    bool iPol = iLit->isPositive();
    for(unsigned j=0; j<hlen; j++) {
      if(i==j) {
	continue;
      }
      Literal* jLit = (*cl)[j];
      unsigned jPred = jLit->functor();
      bool jPol = jLit->isPositive();

      slits.reset();
      slits.push(SATLiteral(pred2var(iPred), !iPol));
      slits.push(SATLiteral(pred2var(jPred), !jPol));

      if(slits[0]==slits[1].opposite()) { continue; }
      if(slits[0]==slits[1]) { slits.pop(); }

      SATClause* scl = SATClause::fromStack(slits);
      _satPrb.push(scl);

//      LOG(scl->toString()<<" <-- "<<iLit->toString()<<", "<<jLit->toString());
    }
  }
}

}


