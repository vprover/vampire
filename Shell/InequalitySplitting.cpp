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
#include "Kernel/ApplicativeHelper.hpp"
#include "Kernel/TermIterators.hpp"

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
: _splittingTreshold(opt.inequalitySplitting()), _appify(false)
{
  ASS_G(_splittingTreshold,0);
}

void InequalitySplitting::perform(Problem& prb)
{
  CALL("InequalitySplitting::perform");

  _appify = prb.hasApp();
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

  UnitInputType inpType = cl->inputType();
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

  Clause* res = new(clen) Clause(clen,NonspecificInferenceMany(InferenceRule::INEQUALITY_SPLITTING, premises));
  res->setAge(cl->age()); // MS: this seems useless; as long as InequalitySplitting is only operating as a part of preprocessing, age is going to 0 anyway

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

Literal* InequalitySplitting::splitLiteral(Literal* lit, UnitInputType inpType, Clause*& premise)
{
  CALL("InequalitySplitting::splitLiteral");
  ASS(isSplittable(lit));

  TermList srt = SortHelper::getEqualityArgumentSort(lit);
  TermStack vars;

  VariableIterator vit(srt);
  while(vit.hasNext()){
    vars.push(vit.next());
  }

  SortHelper::normaliseSort(vars, srt);

  unsigned fun;
  OperatorType* type;
  if(!_appify){
    fun=env.signature->addNamePredicate(vars.size() + 1);
    type = OperatorType::getPredicateType({srt}, vars.size());
  } else {
    srt = AtomicSort::arrowSort(srt, AtomicSort::boolSort());
    fun=env.signature->addNameFunction(vars.size());
    type = OperatorType::getConstantsType(srt, vars.size());
  }


  Signature::Symbol* sym;
  if(_appify){
    sym = env.signature->getFunction(fun);    
  } else {
    sym = env.signature->getPredicate(fun);    
  }
  sym->setType(type);

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
    sym->addColor(t.term()->color());
  }
  if(env.colorUsed && t.term()->skip()) {
    sym->markSkip();
  }

  Clause* defCl=new(1) Clause(1,NonspecificInference0(inpType,InferenceRule::INEQUALITY_SPLITTING_NAME_INTRODUCTION));
  (*defCl)[0]=makeNameLiteral(fun, t, false, vars);
  _predDefs.push(defCl);

  InferenceStore::instance()->recordIntroducedSymbol(defCl,false,fun);

  premise=defCl;

  env.statistics->splitInequalities++;

  return makeNameLiteral(fun, s, true, vars);
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

Literal* InequalitySplitting::makeNameLiteral(unsigned predNum, TermList arg, bool polarity, TermStack vars)
{
  CALL("InequalitySplitting::makeNameLiteral");
 
  if(!_appify){
    vars.push(arg);
    return Literal::create(predNum, vars.size(), polarity, false, vars.begin());
  } else {
    TermList boolT = polarity ? TermList(Term::foolTrue()) : TermList(Term::foolFalse());
    TermList head = TermList(Term::create(predNum, vars.size(), vars.begin()));
    TermList headS = SortHelper::getResultSort(head.term());
    TermList t = ApplicativeHelper::createAppTerm(headS, head, arg);
    return Literal::createEquality(true, t, boolT, AtomicSort::boolSort());
  }

}


}
