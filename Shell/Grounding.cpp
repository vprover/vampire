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
 * @file Grounding.cpp
 * Implements class Grounding.
 */

#include "Lib/Environment.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"

#include "Grounding.hpp"

namespace Shell
{

using namespace Lib;
using namespace Kernel;

Grounding::GroundingApplicator::GroundingApplicator()
{
  int funcs=env.signature->functions();
  for(int i=0;i<funcs;i++) {
    if(env.signature->functionArity(i)==0) {
      if(env.signature->getFunction(i)->fnType()->result()!= AtomicSort::defaultSort()){
        USER_ERROR("grounding mode can (currently) only be used on unsorted problems, problem with "+env.signature->functionName(i));
      }
      _constants.push(TermList(Term::create(i,0,0)));
    }
  }
  if(_constants.size()) {
    _maxIndex=_constants.size()-1;
  }
}

void Grounding::GroundingApplicator::initForClause(Clause* cl)
{
  _varNumbering.reset();
  int nextNum=0;
  unsigned clen=cl->length();
  for(unsigned i=0;i<clen;i++) {
    Literal* lit=(*cl)[i];
    VariableIterator vit(lit);
    while(vit.hasNext()) {
      unsigned var=vit.next().var();
      if(_varNumbering.insert(var,nextNum)) {
	nextNum++;
      }
    }
  }
  _varCnt=nextNum;
  _indexes.init(_varCnt, 0);
  _beforeFirst=true;
}

bool Grounding::GroundingApplicator::newAssignment()
{
  if(_beforeFirst) {
    _beforeFirst=false;
    return _constants.size()>0 || _varCnt==0;
  }
  int incIndex=_varCnt-1;
  while(incIndex>=0 && _indexes[incIndex]==_maxIndex) {
    _indexes[incIndex]=0;
    incIndex--;
  }
  if(incIndex==-1) {
    return false;
  }
  _indexes[incIndex]++;
  return true;
}

TermList Grounding::GroundingApplicator::apply(unsigned var)
{
  return _constants[_indexes[_varNumbering.get(var)]];
}

ClauseList* Grounding::ground(Clause* cl)
{
  CALL("Grounding::ground");

  ClauseList* res=0;

  unsigned clen=cl->length();

  _ga.initForClause(cl);
  while(_ga.newAssignment()) {
    Clause* rcl=new(clen) Clause(clen, NonspecificInference1(InferenceRule::GROUNDING, cl));
    rcl->setAge(cl->age());

    for(unsigned i=0;i<clen;i++) {
      (*rcl)[i]=SubstHelper::apply((*cl)[i], _ga);
    }

    ClauseList::push(rcl, res);
  }

  return res;
}


ClauseList* Grounding::simplyGround(ClauseIterator clauses)
{
  CALL("Grounding::simplyGround");

  Grounding g;
  ClauseList* res=0;

  while(clauses.hasNext()) {
    Clause* cl=clauses.next();
    ClauseList::concat(g.ground(cl), res);
  }

  return res;
}

void Grounding::getLocalEqualityAxioms(TermList sort, bool otherThanReflexivity, ClauseList*& acc)
{
  CALL("Grounding::getLocalEqualityAxioms");

  Clause* axR = new(1) Clause(1, NonspecificInference0(UnitInputType::AXIOM,InferenceRule::EQUALITY_AXIOM));
  (*axR)[0]=Literal::createEquality(true, TermList(0,false),TermList(0,false), sort);
  ClauseList::push(axR, acc);

  //we do not need to add symmetry because that is taken care of by argument order
  //normalization

  if(otherThanReflexivity) {
    Clause* axT = new(3) Clause(3, NonspecificInference0(UnitInputType::AXIOM,InferenceRule::EQUALITY_AXIOM));
    (*axT)[0]=Literal::createEquality(false,TermList(0,false),TermList(1,false), sort);
    (*axT)[1]=Literal::createEquality(false,TermList(0,false),TermList(2,false), sort);
    (*axT)[2]=Literal::createEquality(true,TermList(2,false),TermList(1,false), sort);
    ClauseList::push(axT, acc);
  }
}

ClauseList* Grounding::getEqualityAxioms(bool otherThanReflexivity)
{
  CALL("Grounding::addEqualityAxioms");

  ClauseList* res=0;

/*
  unsigned sortCnt = env.sorts->sorts();
  for(unsigned i=0; i<sortCnt; ++i) {
    getLocalEqualityAxioms(i, otherThanReflexivity, res);
  }
*/
  getLocalEqualityAxioms(AtomicSort::defaultSort(), otherThanReflexivity, res);

  if(otherThanReflexivity) {

    DArray<TermList> args;
    int preds=env.signature->predicates();
    for(int pred=1;pred<preds;pred++) { //we skip equality predicate, as transitivity was added above
      unsigned arity=env.signature->predicateArity(pred);
      if(arity==0) {
        continue;
      }

      OperatorType* predType = env.signature->getPredicate(pred)->predType();

      args.ensure(arity);
      for(unsigned i=0;i<arity;i++) {
        args[i]=TermList(i+2, false);
      }

      for(unsigned i=0;i<arity;i++) {

        Literal* eqLit=Literal::createEquality(false, TermList(0,false),TermList(1,false), predType->arg(i));

        Clause* axCong = new(3) Clause(3, NonspecificInference0(UnitInputType::AXIOM,InferenceRule::EQUALITY_AXIOM));
        (*axCong)[0]=eqLit;

        TermList iArg=args[i];
        args[i]=TermList(0,false);
        (*axCong)[1]=Literal::create(pred, arity, false, false, args.array());
        args[i]=TermList(1,false);
        (*axCong)[2]=Literal::create(pred, arity, true, false, args.array());
        args[i]=iArg;

        ClauseList::push(axCong,res);
      }
    }
  }

  return res;
}


}
