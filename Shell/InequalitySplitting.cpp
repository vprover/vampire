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

#include "Lib/Environment.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/HOL/HOL.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"

#include "Options.hpp"
#include "Statistics.hpp"

#include "InequalitySplitting.hpp"

#define TRACE_INEQUALITY_SPLITTING 0

namespace Shell
{

using namespace std;
using namespace Lib;
using namespace Kernel;


InequalitySplitting::InequalitySplitting(const Options& opt)
: _splittingTreshold(opt.inequalitySplitting()), _appify(false)
{
  ASS_G(_splittingTreshold,0);
}

void InequalitySplitting::perform(Problem& prb)
{
  _appify = prb.hasApp();
  if(perform(prb.units())) {
    prb.invalidateByRemoval();
  }
}

bool InequalitySplitting::perform(UnitList*& units)
{
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

  // static DArray<Literal*> resLits(8);
  RStack<Literal*> resLits;

  UnitInputType inpType = cl->inputType();
  UnitList* premises=0;

  for(unsigned i=0; i<firstSplittable; i++) {
    resLits->push((*cl)[i]);
  }
  for(unsigned i=firstSplittable; i<clen; i++) {
    Literal* lit= (*cl)[i];
    if(i==firstSplittable || isSplittable(lit)) {
      Clause* prem;
      resLits->push(splitLiteral(lit, inpType , prem));
      UnitList::push(prem, premises);
    } else {
      resLits->push(lit);
    }
  }

  UnitList::push(cl, premises);

  auto res = Clause::fromStack(*resLits,NonspecificInferenceMany(InferenceRule::INEQUALITY_SPLITTING, premises));
  // TODO isn't this done automatically?
  res->setAge(cl->age()); // MS: this seems useless; as long as InequalitySplitting is only operating as a part of preprocessing, age is going to 0 anyway

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
  sym->markProtected(); // at least to prevent blocked clause elimination to work on split equality (think "Problems/ARI/ARI713_1.p --decode ott+2_1:1_bce=on:ins=3_0", where BCE otherwise wipes the input completely)

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

  RStack<Literal*> resLits;
  auto defCl = Clause::fromLiterals({makeNameLiteral(fun, t, false, vars)}, 
      NonspecificInference0(inpType,InferenceRule::INEQUALITY_SPLITTING_NAME_INTRODUCTION));
  _predDefs.push(defCl);

  if(_appify){
    InferenceStore::instance()->recordIntroducedSymbol(defCl,SymbolType::FUNC,fun);
  } else {
    InferenceStore::instance()->recordIntroducedSymbol(defCl,SymbolType::PRED,fun);
  }

  premise=defCl;

  env.statistics->splitInequalities++;

  return makeNameLiteral(fun, s, true, vars);
}

bool InequalitySplitting::isSplittable(Literal* lit)
{
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
  if(!_appify){
    vars.push(arg);
    return Literal::create(predNum, vars.size(), polarity, vars.begin());
  } else {
    TermList boolT = polarity ? TermList(Term::foolTrue()) : TermList(Term::foolFalse());
    TermList head = TermList(Term::create(predNum, vars.size(), vars.begin()));
    TermList t = HOL::create::app(head, arg);
    return Literal::createEquality(true, t, boolT, AtomicSort::boolSort());
  }

}


}
