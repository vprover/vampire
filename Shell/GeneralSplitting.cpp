
/*
 * File GeneralSplitting.cpp.
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
 * @file GeneralSplitting.cpp
 * Implements class GeneralSplitting.
 */

#include "GeneralSplitting.hpp"

#include "Lib/DArray.hpp"
#include "Lib/DHMultiset.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Set.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Unit.hpp"

#include "Kernel/ApplicativeHelper.hpp"

namespace Shell
{

using namespace Lib;
using namespace Kernel;

void GeneralSplitting::apply(Problem& prb)
{
  CALL("GeneralSplitting::apply(Problem&)");
  _appify = prb.hasApp();
  if(apply(prb.units())) {
    prb.invalidateProperty();
  }
}

/**
 * Perform general splitting on clauses in @c units and return true if successful
 */
bool GeneralSplitting::apply(UnitList*& units)
{
  CALL("GeneralSplitting::apply(UnitList*&)");

  bool modified = false;

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
      modified = true;
      uit.del();
      UnitList::push(cl, splitRes);
    }
  }
  ASS_EQ(modified, UnitList::isNonEmpty(splitRes));
  units=UnitList::concat(splitRes, units);
  return modified;
}

/**
 * Perform general splitting on clauses in @c clauses and return true if successful
 * TODO fix sharing with apply(UnitList)
 */
bool GeneralSplitting::apply(ClauseList*& clauses)
{
  CALL("GeneralSplitting::apply(UnitList*&)");

  bool modified = false;

  UnitList* splitRes=0;

  ClauseList::DelIterator cit(clauses);
  while(cit.hasNext()) {
    Clause* cl=cit.next();
    bool performed=false;
    while(apply(cl, splitRes)) {
      performed=true;
    }
    if(performed) {
      modified = true;
      cit.del();
      UnitList::push(cl, splitRes);
    }
  }
  ASS_EQ(modified, UnitList::isNonEmpty(splitRes));
  ClauseList* splitResC = 0;
  ClauseList::pushFromIterator(getStaticCastIterator<Clause*>(UnitList::Iterator(splitRes)),splitResC);
  clauses=ClauseList::concat(splitResC, clauses);
  return modified;
}

/**
 * Find variable that occurs in literals with the smallest number
 * of other variables, and split out into a new clause all the literals
 * that contain this variable. (The name predicate will then have all
 * these variables that accompany our variable in some literal as its
 * arguments)
 */
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

    //TODO can move varCnt check to here!

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

  unsigned varCnt=vars.size();
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

  static Stack<TermList> args;
  static Stack<TermList> termArgs;
  static Stack<TermList> argSorts;
  args.reset();
  termArgs.reset();
  argSorts.reset();

  DHMap<unsigned,TermList> varSorts;
  SortHelper::collectVariableSorts(cl, varSorts);

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
      TermList argSort = varSorts.get(var);
      if(argSort == Term::superSort()){
        args.push(TermList(var, false));//TODO check that this works
      } else {
        termArgs.push(TermList(var, false));
        argSorts.push(argSort);
      }
    }
  }
  ASS(termArgs.size() == argSorts.size());


  VList* vl = VList::empty();
  for(int i = args.size() -1; i >= 0 ; i--){
    VList::push(args[i].var(), vl);
  }
  for(unsigned i = 0; i < termArgs.size() && !_appify; i++){
    args.push(termArgs[i]);
  }

  unsigned namingFun = _appify ? env.signature->addNameFunction(args.size()) :
                                 env.signature->addNamePredicate(minDeg); 
  TermList sort;
  if(_appify){
    sort = Term::arrowSort(argSorts, Term::boolSort());
    OperatorType* ot = OperatorType::getConstantsType(sort, vl);
    env.signature->getFunction(namingFun)->setType(ot);  
  }else{
    OperatorType* ot = 
    OperatorType::getPredicateType(minDeg - VList::length(vl), argSorts.begin(), vl);
    env.signature->getPredicate(namingFun)->setType(ot);
  }

  /*if(mdvColor!=COLOR_TRANSPARENT && otherColor!=COLOR_TRANSPARENT) {
    ASS_EQ(mdvColor, otherColor);
    env.signature->getPredicate(namingPred)->addColor(mdvColor);
  }
  if(env.colorUsed && cl->skip()) {
    env.signature->getPredicate(namingPred)->markSkip();
  }*/

  Literal* pnLit;
  Literal* nnLit;
  if(_appify){
    TermList head = TermList(Term::create(namingFun, args.size(), args.begin()));
    TermList t = ApplicativeHelper::createAppTerm(sort, head, termArgs);
    pnLit=Literal::createEquality(true, t, TermList(Term::foolTrue()), Term::boolSort()); 
    nnLit=Literal::createEquality(true, t, TermList(Term::foolFalse()), Term::boolSort());
  } else {
    ASS_EQ(args.size(), minDeg);
    pnLit=Literal::create(namingFun, minDeg, true, false, args.begin());
    nnLit=Literal::create(namingFun, minDeg, false, false, args.begin());  
  }
  otherLits.push(nnLit);
  mdvLits.push(pnLit);

  Clause* mdvCl=Clause::fromStack(mdvLits, cl->inputType(), new Inference(Inference::GENERAL_SPLITTING_COMPONENT));
  mdvCl->setAge(cl->age());
  UnitList::push(mdvCl, resultStack);

  InferenceStore::instance()->recordSplittingNameLiteral(mdvCl, pnLit);
  if(env.clausePriorities){
    env.clausePriorities->insert(mdvCl,cl->getPriority());
  }

  Clause* otherCl=Clause::fromStack(otherLits, cl->inputType(), new Inference2(Inference::GENERAL_SPLITTING, cl, mdvCl));
  otherCl->setAge(cl->age());

  cl=otherCl;

  return true;
}

}
