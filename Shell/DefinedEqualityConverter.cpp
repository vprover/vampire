
/*
 * File DefinedEqualityConverter.cpp.
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
 * @file DefinedEqualityConverter.cpp
 * Implements class DefinedEqualityConverter.
 */

#include "Lib/DArray.hpp"
#include "Lib/Environment.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/Substitution.hpp"
#include "Kernel/Sorts.hpp"
#include "Kernel/SortHelper.hpp"

#include "Indexing/TermSharing.hpp"

#include "Shell/LambdaElimination.hpp"

#include "Statistics.hpp"

#include "DefinedEqualityConverter.hpp"

namespace Shell
{

using namespace Lib;
using namespace Kernel;


DefinedEqualityConverter::DefinedEqualityConverter()
{}

void DefinedEqualityConverter::convert(Problem& prb)
{
  CALL("DefinedEqualityConverter::convert");

  convert(prb.units());

}

void DefinedEqualityConverter::convert(UnitList*& units)
{
  CALL("DefinedEqualityConverter::convert");

  UnitList::DelIterator uit(units);
  while(uit.hasNext()) {
    Clause* cl=static_cast<Clause*>(uit.next());
    ASS_REP(cl->isClause(), *cl);
    Clause* cl2=findAndConvert(cl);
    if(cl2) {
      uit.insert(cl2);
    }
  }

}

Clause* DefinedEqualityConverter::findAndConvert(Clause* c)
{
  CALL("DefinedEqualityConverter::findAndConvert");

  //static 
  VarOccMap vom;
  //vom.reset();

  //static 
  Substitution subst;
  //subst.reset(); 

  Stack<Literal*> added;
  Set<Literal*> removed;

  bool addedToSub = false;

  unsigned numRemoved = 0;
  unsigned side;

  LeibEqRec ler;

  unsigned length = c->length();
  for (int i = length - 1; i >= 0; i--) {
    Literal *lit = (*c)[i];
    if(isAndrewsEquality(lit, side)){
      numRemoved++;
      removed.insert(lit);
      TermList def = getAndrewsDef(lit, side);
      unsigned definedVar = getVar(lit, side);
      subst.bind(definedVar, def);
      addedToSub = true;
    }else if(isLeibnizEquality(lit, ler)){
      LeibEqRec ler2;
      TermList dum;
      if(!subst.findBinding(ler.var, dum) && vom.find(ler.var, ler2)){
        if(ler.polarity != ler2.polarity){
          //found a defined equality
          removed.insert(ler.lit);
          removed.insert(ler2.lit);

          Literal* newLit = createEquality(ler, ler2);
          added.push(newLit);

          numRemoved++;

          TermList def; 
          unsigned definedVar;
          if(!ler.polarity){
           definedVar = ler.var;
           def = getLeibnizDef(ler);
          } else {
           ASS(!ler2.polarity);
           definedVar = ler2.var;
           def = getLeibnizDef(ler2);
          }
          
          subst.bind(definedVar, def);
          addedToSub = true;
        }
      } else {
        vom.insert(ler.var, ler);
      }
    }
  }

  if(addedToSub){
    unsigned newLen = length - numRemoved;

    Inference* inf = new Inference1(Inference::DEFINED_TO_PRIMITIVE_EQUALITY, c);
    Clause* res = new(newLen) Clause(newLen, c->inputType(), inf);

    unsigned n = 0;
    while(!added.isEmpty()){
      Literal* curr = added.pop();
      (*res)[n++] = curr->apply(subst);
    }

    for(unsigned i=0;i<length;i++) {
      Literal* curr=(*c)[i];
      if(!removed.contains(curr)) {
        (*res)[n++] = curr->apply(subst);
      } else {
        removed.remove(curr);
      }
    }
    ASS_EQ(n,newLen);

    res->setAge(c->age()+1);
    env.statistics->definedEqualities += numRemoved;

    return res;
  }

  return 0;

}

bool DefinedEqualityConverter::isAndrewsEquality(Literal* l, unsigned& side){
  CALL("DefinedEqualityConverter::isAndrewsEquality");

  if(!l->isEquality()){ return false; }

  unsigned sort = SortHelper::getEqualityArgumentSort(l);
  if(!(sort == Sorts::SRT_BOOL)){
    return false;
  }
  TermList* arg1 = l->args();
  TermList* arg2 = arg1->next();
  TermList* tm;

  int i1 = PE::isBoolValue(*arg1);
  int i2 = PE::isBoolValue(*arg2);

  if(!(i1 > -1)){
    if(!(i2 > -1)){
      return false;
    }
    if(i2 == l->polarity()){ return false; }
    side = 0;
    tm = arg1;
  } else {
    if(i1 == l->polarity()){ return false; }
    side = 1;
    tm = arg2;
  }

  TermList head = HSH::getHead(*tm);
  unsigned argNum = HSH::argNum(*tm);
  if(!head.isVar() || argNum != 2){
    return false;
  }

  TermList firstArg = HSH::getNthArg(*tm, 0);
  TermList secondArg = HSH::getNthArg(*tm, 1);

  if(!TermList::equals(firstArg, secondArg)){
    return false;
  }

  return true;
}


/* At current point, procedure is not compatible with usage of axioms
   as takes place after clausefication*/
TermList DefinedEqualityConverter::getAndrewsDef(Literal* l, unsigned side){
  CALL("DefinedEqualityConverter::getAndrewsDef");
  
  TermList* tl = l->nthArgument(side);
  unsigned sort = HSH::getNthArgSort(*tl, 0);
  unsigned equalsSort = env.sorts->addFunctionSort(sort, Sorts::SRT_BOOL);
  equalsSort = env.sorts->addFunctionSort(sort, equalsSort);
  
  bool added;
  return LambdaElimination::addHolConstant("vEQUALS", equalsSort, added, SS::EQUALS);
}

unsigned DefinedEqualityConverter::getVar(Literal* l, unsigned side){
  CALL("DefinedEqualityConverter::getVar");

  TermList* tl = l->nthArgument(side);
  TermList head = HSH::getHead(*tl);
  ASS(head.isVar()); 
  
  return head.var();
}

bool DefinedEqualityConverter::isLeibnizEquality(Literal* l, LeibEqRec& ler){
  CALL("DefinedEqualityConverter::isLeibnizEquality");
 
  if(!l->isEquality()){ return false; }

  unsigned sort = SortHelper::getEqualityArgumentSort(l);
  if(!(sort == Sorts::SRT_BOOL)){
    return false;
  }
  TermList* arg1 = l->args();
  TermList* arg2 = arg1->next();
  TermList* tm;

  int i1 = PE::isBoolValue(*arg1);
  int i2 = PE::isBoolValue(*arg2);

  if(!(i1 > -1)){
    if(!(i2 > -1)){
      return false;
    }
    ler.polarity = (i2 == l->polarity());
    ler.side = 0;
    tm = arg1;
  } else {
    ler.polarity = (i1 == l->polarity());
    ler.side = 1;
    tm = arg2;
  }

  TermList head = HSH::getHead(*tm);
  unsigned argNum = HSH::argNum(*tm);
  if(!head.isVar() || argNum != 1){
    return false;
  }

  ler.var = head.var();
  ler.arg = HSH::getNthArg(*tm, 0);
 
  //fail on occurs
  TermIterator varIt = Term::getVariableIterator(ler.arg);
  while(varIt.hasNext()){
    TermList var = varIt.next();
    if(var.var() == ler.var){
      return false;
    }
  }

  ler.argSort = HSH::getNthArgSort(*tm,0);
  ler.lit = l;

  return true;
}

Literal* DefinedEqualityConverter::createEquality(LeibEqRec ler1, LeibEqRec ler2){
  CALL("DefinedEqualityConverter::createEquality");

  TermList* t1 = ler1.lit->nthArgument(ler1.side);
  TermList* t2 = ler2.lit->nthArgument(ler2.side);

  unsigned sort = HSH::getNthArgSort(*t1, 0);

  return Literal::createEquality(true, HSH::getNthArg(*t1, 0), HSH::getNthArg(*t2, 0), sort);
}

TermList DefinedEqualityConverter::getLeibnizDef(LeibEqRec ler){
  CALL("DefinedEqualityConverter::getLeibnizDef"); 

  unsigned equalsSort = env.sorts->addFunctionSort(ler.argSort, Sorts::SRT_BOOL);
  equalsSort = env.sorts->addFunctionSort(ler.argSort, equalsSort);
  
  bool added;
  TermList constant = LambdaElimination::addHolConstant("vEQUALS", equalsSort, added, SS::EQUALS);
  return HSH::apply(constant, equalsSort, ler.arg, ler.argSort);
}

}
