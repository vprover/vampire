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
 * @file DistinctProcessor.cpp
 * Implements class DistinctProcessor.
 */

#include "DistinctProcessor.hpp"

#include "Lib/Environment.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Unit.hpp"

#include <cstring>

namespace Shell
{

//TODO: add expansion of non-top-level and negative distinct predicates

/**
 * True if 
 */
bool DistinctProcessor::isDistinctPred(Literal* l)
{
  CALL("DistinctProcessor::isDistinctPred");

  //this is a hacky way to check for disctnct predicates,
  //needs to be fixed once we have a proper sopport for
  //these in the signature

  //Moreover, this check turned out to be bottleneck, so it
  //had to be optimized. The original was:
  //return l->predicateName().substr(0,9)=="$distinct"
  const char* n = l->predicateName().c_str();
  return n[0]=='$' && memcmp(n+1,"distinct",8)==0;
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
      }else{
        USER_ERROR("$distinct should only be used positively with constants");
      }
    }
  }

  return false;
}

bool DistinctProcessor::apply(Clause* cl, Unit*& res) {
  return false;
}

}
