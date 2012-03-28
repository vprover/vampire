/**
 * @file DistinctProcessor.cpp
 * Implements class DistinctProcessor.
 */

#include "Lib/Environment.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Unit.hpp"

#include "DistinctProcessor.hpp"

namespace Shell
{

//TODO: add expansion of non-top-level and negative distinct predicates

bool DistinctProcessor::isDistinctPred(Literal* l)
{
  CALL("DistinctProcessor::isDistinctPred");

  //this is a hacky way to check for disctnct predicates,
  //needs to be fixed once we have a proper sopport for
  //these in the signature
  return l->predicateName().substr(0,9)=="$distinct";
}

bool DistinctProcessor::apply(FormulaUnit* unit, Unit*& res)
{
  CALL("DistinctProcessor::apply");

  Formula* form = unit->formula();


  static Stack<unsigned> distConsts;
  if(form->connective()==LITERAL) {
    Literal* tlLit = form->literal();
    if(isDistinctPred(tlLit) && tlLit->isPositive()) {
      distConsts.reset();
      bool justConsts = true;
      Literal::Iterator argIt(tlLit);
      while(argIt.hasNext()) {
	TermList a = argIt.next();
	if(!a.isTerm() || a.term()->arity()!=0) {
	  justConsts = false;
	  break;
	}
	distConsts.push(a.term()->functor());
      }

      if(justConsts) {
	unsigned grpIdx = env.signature->createDistinctGroup(unit);
	while(distConsts.isNonEmpty()) {
	  env.signature->addToDistinctGroup(distConsts.pop(), grpIdx);
	}
      }
    }
  }

  return false;
}

bool DistinctProcessor::apply(Clause* cl, Unit*& res) {
  return false;
}

}
