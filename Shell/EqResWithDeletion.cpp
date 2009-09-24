/**
 * @file EqResWithDeletion.cpp
 * Implements class EqResWithDeletion.
 */

#include "../Kernel/Clause.hpp"
#include "../Kernel/Inference.hpp"
#include "../Kernel/SubstHelper.hpp"
#include "../Kernel/Term.hpp"
#include "../Kernel/Unit.hpp"

#include "EqResWithDeletion.hpp"

namespace Shell
{

using namespace Lib;
using namespace Kernel;

void EqResWithDeletion::apply(UnitList*& units)
{
  CALL("EqResWithDeletion::apply(UnitList*&)");

  UnitList::DelIterator uit(units);
  while(uit.hasNext()) {
    Clause* cl=static_cast<Clause*>(uit.next());
    ASS(cl->isClause());
    Clause* cl2=apply(cl);
    if(cl!=cl2) {
      uit.replace(cl2);
    }
  }
}


Clause* EqResWithDeletion::apply(Clause* cl)
{
  CALL("EqResWithDeletion::apply(Clause*)");

start_applying:

  unsigned clen=cl->length();

  _subst.reset();

  static Stack<Literal*> resLits(8);
  resLits.reset();

  bool foundResolvable=false;
  for(unsigned i=0;i<clen;i++) {
    Literal* lit=(*cl)[i];
    if(!foundResolvable && scan(lit)) {
      foundResolvable=true;
    } else {
      resLits.push(lit);
    }
  }
  if(!foundResolvable) {
    return cl;
  }

  unsigned nlen=resLits.size();
  ASS_L(nlen, clen);

  Inference* inf = new Inference1(Inference::EQUALITY_RESOLUTION, cl);
  Clause* res = new(nlen) Clause(nlen, cl->inputType(), inf);
  res->setAge(cl->age());

  for(unsigned i=0;i<nlen;i++) {
    (*res)[i] = SubstHelper::apply(resLits[i], *this);
  }

  cl=res;
  goto start_applying;
}

TermList EqResWithDeletion::apply(unsigned var)
{
  TermList res;
  if(_subst.find(var, res)) {
    return res;
  } else {
    return TermList(var, false);
  }
}

bool EqResWithDeletion::scan(Literal* lit)
{
  CALL("EqResWithDeletion::scan(Literal*)");

  if(lit->isEquality() && lit->isNegative()) {
    TermList t0=*lit->nthArgument(0);
    TermList t1=*lit->nthArgument(1);
    if( t0.isVar() && !t1.containsSubterm(t0) ) {
      if(_subst.insert(t0.var(), t1)) {
	return true;
      }
    }
    if( t1.isVar() && !t0.containsSubterm(t1) ) {
      if(_subst.insert(t1.var(), t0)) {
	return true;
      }
    }
  }
  return false;

}

}
