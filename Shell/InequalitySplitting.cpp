
/*
 * File InequalitySplitting.cpp.
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
 * @file InequalitySplitting.cpp
 * Implements class InequalitySplitting.
 */

#include "Lib/DArray.hpp"
#include "Lib/Environment.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Unit.hpp"

#include "Indexing/TermSharing.hpp"

#include "Options.hpp"
#include "Statistics.hpp"

#include "InequalitySplitting.hpp"

#define TRACE_INEQUALITY_SPLITTING 0

namespace Shell
{

using namespace Lib;
using namespace Kernel;


InequalitySplitting::InequalitySplitting(const Options& opt)
: _splittingTreshold(opt.inequalitySplitting())
{
  ASS_G(_splittingTreshold,0);
}

void InequalitySplitting::perform(Problem& prb)
{
  CALL("InequalitySplitting::perform");

  if(perform(prb.units())) {
    prb.invalidateByRemoval();
  }
}

bool InequalitySplitting::perform(UnitList*& units)
{
  CALL("InequalitySplitting::perform");

  bool modified = false;

  UnitList::DelIterator uit(units);
  while(uit.hasNext()) {
    Clause* cl=static_cast<Clause*>(uit.next());
    ASS_REP(cl->isClause(), *cl);
    Clause* cl2=trySplitClause(cl);
    if(cl2!=cl) {
      modified = true;
      uit.replace(cl2);
    }
  }

  while(_predDefs.isNonEmpty()) {
    ASS(modified);
    uit.insert(_predDefs.pop());
  }
  return modified;
}

Clause* InequalitySplitting::trySplitClause(Clause* cl)
{
  CALL("InequalitySplitting::trySplitClause");
  ASS(cl);

  unsigned clen=cl->length();

  unsigned firstSplittable=clen;
  for(unsigned i=0;i<clen;i++) {
    if(isSplittable( (*cl)[i] )) {
      firstSplittable=i;
      break;
    }
  }
  if(firstSplittable==clen) {
    return cl;
  }

  static DArray<Literal*> resLits(8);
  resLits.ensure(clen);

  Unit::InputType inpType = cl->inputType();
  UnitList* premises=0;

  for(unsigned i=0; i<firstSplittable; i++) {
    resLits[i] = (*cl)[i];
  }
  for(unsigned i=firstSplittable; i<clen; i++) {
    Literal* lit= (*cl)[i];
    if(i==firstSplittable || isSplittable(lit)) {
      Clause* prem;
      resLits[i] = splitLiteral(lit, inpType , prem);
      UnitList::push(prem, premises);
    } else {
      resLits[i] = lit;
    }
  }

  UnitList::push(cl, premises);
  Inference* inf = new InferenceMany(Inference::INEQUALITY_SPLITTING, premises);

  Clause* res = new(clen) Clause(clen, inpType, inf);
  res->setAge(cl->age());

  for(unsigned i=0;i<clen;i++) {
    (*res)[i] = resLits[i];
  }

#if TRACE_INEQUALITY_SPLITTING
  cout<<"---------"<<endl;
  cout<<"IEQ split from: "<<(*cl)<<endl;
  cout<<"IEQ split to: "<<(*res)<<endl;
  UnitList::Iterator pit(premises);
  ALWAYS(pit.hasNext()); pit.next();
  while(pit.hasNext()) {
    cout<<"IEQ name: "<<pit.next()->toString()<<endl;
  }
#endif

  return res;

}

Literal* InequalitySplitting::splitLiteral(Literal* lit, Unit::InputType inpType, Clause*& premise)
{
  CALL("InequalitySplitting::splitLiteral");
  ASS(isSplittable(lit));

  unsigned predNum=env.signature->addNamePredicate(1);
  unsigned srt = SortHelper::getEqualityArgumentSort(lit);
  OperatorType* type = OperatorType::getPredicateType({srt});

  Signature::Symbol* predSym = env.signature->getPredicate(predNum);
  predSym->setType(type);

  TermList s;
  TermList t; //the ground inequality argument, that'll be split out
  if( isSplittableEqualitySide(*lit->nthArgument(0)) ) {
    s=*lit->nthArgument(1);
    t=*lit->nthArgument(0);
  } else {
    ASS(isSplittableEqualitySide(*lit->nthArgument(1)));
    s=*lit->nthArgument(0);
    t=*lit->nthArgument(1);
  }

  ASS(t.isTerm());
  if(env.colorUsed && t.term()->color()!=COLOR_TRANSPARENT) {
    predSym->addColor(t.term()->color());
  }
  if(env.colorUsed && t.term()->skip()) {
    predSym->markSkip();
  }

  Inference* inf = new Inference0(Inference::INEQUALITY_SPLITTING_NAME_INTRODUCTION);
  Clause* defCl=new(1) Clause(1, inpType, inf);
  (*defCl)[0]=makeNameLiteral(predNum, t, false);
  _predDefs.push(defCl);

  InferenceStore::instance()->recordIntroducedSymbol(defCl,false,predNum);

  premise=defCl;

  env.statistics->splitInequalities++;

  return makeNameLiteral(predNum, s, true);

}

bool InequalitySplitting::isSplittable(Literal* lit)
{
  CALL("InequalitySplitting::isSplittable");

  return lit->isEquality() && lit->isNegative() &&
	(isSplittableEqualitySide(*lit->nthArgument(0)) ||
		isSplittableEqualitySide(*lit->nthArgument(1)));
}

bool InequalitySplitting::isSplittableEqualitySide(TermList t)
{
  return t.isTerm() && t.term()->ground() && t.term()->weight()>=_splittingTreshold;
}

Literal* InequalitySplitting::makeNameLiteral(unsigned predNum, TermList arg, bool polarity)
{
  CALL("InequalitySplitting::makeNameLiteral");

  return Literal::create(predNum, 1, polarity, false, &arg);
}


}
