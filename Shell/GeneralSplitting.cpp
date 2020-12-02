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

  static TermStack args;
  args.reset();
  static TermStack argSorts;
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
      args.push(TermList(var, false));
      argSorts.push(varSorts.get(var));
    }
  }


  unsigned namingPred=env.signature->addNamePredicate(minDeg);
  OperatorType* npredType = OperatorType::getPredicateType(minDeg, argSorts.begin());
  env.signature->getPredicate(namingPred)->setType(npredType);

  if(mdvColor!=COLOR_TRANSPARENT && otherColor!=COLOR_TRANSPARENT) {
    ASS_EQ(mdvColor, otherColor);
    env.signature->getPredicate(namingPred)->addColor(mdvColor);
  }
  if(env.colorUsed && cl->skip()) {
    env.signature->getPredicate(namingPred)->markSkip();
  }



  ASS_EQ(args.size(), minDeg);
  Literal* pnLit=Literal::create(namingPred, minDeg, true, false, args.begin());
  mdvLits.push(pnLit);
  Literal* nnLit=Literal::create(namingPred, minDeg, false, false, args.begin());
  otherLits.push(nnLit);

  Clause* mdvCl=Clause::fromStack(mdvLits, NonspecificInference0(cl->inputType(),InferenceRule::GENERAL_SPLITTING_COMPONENT));
  mdvCl->setAge(cl->age());
  UnitList::push(mdvCl, resultStack);

  InferenceStore::instance()->recordSplittingNameLiteral(mdvCl, pnLit);

  Clause* otherCl=Clause::fromStack(otherLits, NonspecificInference2(InferenceRule::GENERAL_SPLITTING, cl, mdvCl));
  otherCl->setAge(cl->age());

  cl=otherCl;

  return true;
}

}
