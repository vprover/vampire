/**
 * @file GeneralSplitting.cpp
 * Implements class GeneralSplitting.
 */

#include "GeneralSplitting.hpp"

#include "../Lib/DArray.hpp"
#include "../Lib/DHMultiset.hpp"
#include "../Lib/Environment.hpp"

#include "../Kernel/Clause.hpp"
#include "../Kernel/Inference.hpp"
#include "../Kernel/Signature.hpp"
#include "../Kernel/Term.hpp"
#include "../Kernel/TermIterators.hpp"
#include "../Kernel/Unit.hpp"

namespace Shell
{

using namespace Lib;
using namespace Kernel;

void GeneralSplitting::apply(UnitList*& units)
{
  CALL("GeneralSplitting::apply(UnitList*&)");

  UnitList* splitRes=0;

  UnitList::DelIterator uit(units);
  while(uit.hasNext()) {
    Clause* cl=static_cast<Clause*>(uit.next());
    ASS(cl->isClause());
    bool performed=false;
    while(apply(cl, splitRes)) {
      performed=true;
    }
    if(performed) {
      uit.del();
      UnitList::push(cl, splitRes);
    }
  }
  units=UnitList::concat(splitRes, units);
}


bool GeneralSplitting::apply(Clause*& cl, UnitList*& resultStack)
{
  CALL("GeneralSplitting::apply");

  unsigned clen=cl->length();
  if(clen<=1) {
    return false;
  }

  Set<unsigned> vars;
  //only edges from lower to higher variable are included
  DHMultiset<pair<unsigned, unsigned> > connections;
  DHMultiset<unsigned> degrees;


  for(unsigned i=0;i<clen;i++) {
    Literal* lit=(*cl)[i];
    Set<unsigned> litVars;

    VariableIterator vit(lit);
    while(vit.hasNext()) {
      litVars.insert(vit.next().var());
    }

    //we insert a complete graph containing variables from the literal
    Set<unsigned>::Iterator sit(litVars);
    while(sit.hasNext()) {
      unsigned v1=sit.next();
      vars.insert(v1);

      Set<unsigned>::Iterator sit2=sit;
      while(sit2.hasNext()) {
	unsigned v2=sit2.next();
	ASS_NEQ(v1,v2);
	bool inserted;
	if(v1>v2) {
	  inserted= connections.insert(make_pair(v2,v1))==1;
	} else {
	  inserted= connections.insert(make_pair(v1,v2))==1;
	}
	if(inserted) {
	  degrees.insert(v1);
	  degrees.insert(v2);
	}
      }
    }
  }

  unsigned varCnt=vars.numberOfElements();
  if(varCnt<=1) {
    //the clause is ground or with just one variable -- splitting won't help
    return false;
  }


  unsigned minDegVar;
  unsigned minDeg=varCnt-1;
  Set<unsigned>::Iterator vit(vars);
  while(vit.hasNext()) {
    unsigned var=vit.next();
    unsigned deg=degrees.multiplicity(var);

    if(deg<minDeg) {
      minDeg=deg;
      minDegVar=var;
    }
  }

  if(minDeg==varCnt-1) {
    //the graph is complete, and so there is no possible
    //benefit from splitting
    return false;
  }

  Stack<Literal*> mdvLits;
  Stack<Literal*> otherLits;
  Color mdvColor=COLOR_TRANSPARENT;
  Color otherColor=COLOR_TRANSPARENT;

  for(unsigned i=0;i<clen;i++) {
    Literal* lit=(*cl)[i];
    if(lit->containsSubterm(TermList(minDegVar, false))) {
      mdvLits.push(lit);
      mdvColor=static_cast<Color>(mdvColor | lit->color());
    } else {
      otherLits.push(lit);
      otherColor=static_cast<Color>(otherColor | lit->color());
    }
  }

  unsigned namingPred=env.signature->addNamePredicate(minDeg);

  if(mdvColor!=COLOR_TRANSPARENT && otherColor!=COLOR_TRANSPARENT) {
    ASS_EQ(mdvColor, otherColor);
    env.signature->getPredicate(namingPred)->addColor(mdvColor);
  }

  if(env.colorUsed && cl->skip()) {
    env.signature->getPredicate(namingPred)->markSkip();
  }


  static DArray<TermList> args(8);
  args.ensure(minDeg);
  unsigned nnext=0;

  DHMultiset<unsigned>::SetIterator nivit(degrees); //iterating just over non-isolated vars
  while(nivit.hasNext()) {
    unsigned var=nivit.next();
    if(minDegVar==var) {
      continue;
    }
    bool found;
    if(var>minDegVar) {
      found=connections.find(make_pair(minDegVar, var));
    } else {
      found=connections.find(make_pair(var, minDegVar));
    }
    if(found) {
      args[nnext++]=TermList(var, false);
    }
  }
  Literal* pnLit=Literal::create(namingPred, minDeg, true, false, args.array());
  mdvLits.push(pnLit);
  Literal* nnLit=Literal::create(namingPred, minDeg, false, false, args.array());
  otherLits.push(nnLit);

  Clause* mdvCl=Clause::fromStack(mdvLits, cl->inputType(), new Inference(Inference::SPLITTING_COMPONENT));
  mdvCl->setAge(cl->age());
  UnitList::push(mdvCl, resultStack);

  Clause* otherCl=Clause::fromStack(otherLits, cl->inputType(), new Inference2(Inference::SPLITTING, cl, mdvCl));
  otherCl->setAge(cl->age());

  cl=otherCl;

  return true;
}

}
