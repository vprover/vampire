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
 * @file SymElOutput.cpp
 * Implements class SymElOutput.
 */

#include "Lib/Environment.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"

#include "SymElOutput.hpp"

namespace Saturation
{

using namespace Lib;
using namespace Kernel;

SymElOutput::SymElOutput()
: _symElNextClauseNumber(0)
{

}

void SymElOutput::init(SaturationAlgorithm* sa)
{
  CALL("SymElOutput::init");

  _sa=sa;
}

void SymElOutput::onAllProcessed()
{
  CALL("SymElOutput::onAllProcessed");

  _symElRewrites.reset();
  _symElColors.reset();
}

void SymElOutput::onInputClause(Clause* c)
{
  CALL("SymElOutput::onInputClause");

  checkForPreprocessorSymbolElimination(c);
}


void SymElOutput::onNonRedundantClause(Clause* c)
{
  CALL("SymElOutput::onNonRedundantClause");

  if(c->color()==COLOR_TRANSPARENT && !c->skip()) {
    Clause* tgt=c;
    Clause* src;
    bool notFound=false;
    do {
      src=tgt;
      if(!_symElRewrites.find(src, tgt)) {
	ASS_EQ(src, c); //not found can happen only at the first iteration
	notFound=true;
	break;
      }
    } while(tgt);
    if(!notFound) {
      //if we use src instead of c in the second argument, we can output non-simplified clauses
      outputSymbolElimination(_symElColors.get(src), c);
    }
  }
  //if(c->color()==COLOR_TRANSPARENT && c->inputType()!=Clause::AXIOM && !c->skip()) {
  //  cout<<"Interesting: "<<c->toNiceString()<<endl;
  //}
}

/**
 * Called for clauses derived in the run of the saturation algorithm
 * for each pair clause-premise
 *
 * The propositional parts of clauses may not be set properly (the
 * clauses are always valid, however), also the function is not called
 * for clause merging (when the non-propositional parts would coincide).
 */
void SymElOutput::onParenthood(Clause* cl, Clause* parent)
{
  CALL("SymElOutput::onParenthood");

  Color pcol=parent->color();
//  Clause::Store pstore=parent->store();

  if(pcol!=COLOR_TRANSPARENT && cl->color()==COLOR_TRANSPARENT) {
    onSymbolElimination(parent->color(), cl);
  }
  if(pcol==COLOR_TRANSPARENT && _symElRewrites.find(parent)) {
    //Only one of clause's premises can be a clause derived since the
    //previous call to the @b onAllProcessed function, so the insertion
    //should always happen.
    //We don't have an assertion check here, however, as in a rare case
    //the same clause object can be "derived" multiple times due to clause
    //sharing in splitting without backtracking.
    _symElRewrites.insert(cl, parent);
  }
}

void SymElOutput::onSymbolElimination(Color eliminated,
					      Clause* c, bool nonRedundant)
{
  CALL("SymElOutput::onSymbolElimination");
  ASS_EQ(c->color(),COLOR_TRANSPARENT);

  if(!c->skip() && c->noSplits()) {
    if(!_symElColors.insert(c,eliminated)) {
      //the clause was already reported for symbol elimination
      return;
    }
    if(nonRedundant) {
      outputSymbolElimination(eliminated, c);
    }
    else {
      _symElRewrites.insert(c,0);
    }
  }
}

void SymElOutput::outputSymbolElimination(Color eliminated, Clause* c)
{
  CALL("SymElOutput::outputSymbolElimination");
  ASS_EQ(c->color(),COLOR_TRANSPARENT);
  ASS(!c->skip());

  env.beginOutput();

  //BDD::instance()->allowDefinitionOutput(false);
  env.out()<<"%";
  if(eliminated==COLOR_LEFT) {
    env.out()<<"Left";
  } else {
    ASS_EQ(eliminated, COLOR_RIGHT);
    env.out()<<"Right";
  }
  env.out()<<" symbol elimination"<<endl;

  vstring cname = "inv"+Int::toString(_symElNextClauseNumber);
  while(env.signature->isPredicateName(cname, 0)) {
    _symElNextClauseNumber++;
    cname = "inv"+Int::toString(_symElNextClauseNumber);
  }

  _printer.printAsClaim(cname, c);

  //BDD::instance()->allowDefinitionOutput(true);
  _symElNextClauseNumber++;

  env.endOutput();
}


void SymElOutput::checkForPreprocessorSymbolElimination(Clause* cl)
{
  CALL("SymElOutput::checkForPreprocessorSymbolElimination");

  if(!env.colorUsed || cl->color()!=COLOR_TRANSPARENT || cl->skip()) {
    return;
  }

  //TODO: it might examine some parts of the proof-tree multiple times,
  //so perhaps some more caching could be used if it's too slow

  Color inputColor=COLOR_TRANSPARENT;

  static DHMap<Unit*, Color> inputFormulaColors;
  static Stack<Unit*> units;
  units.reset();
  units.push(cl);

  while(units.isNonEmpty()) {
    Unit* u=units.pop();
    Inference::Iterator iit=u->inference().iterator();
//    if(u->inference()->rule()==Inference::INPUT ||
//	    u->inference()->rule()==Inference::NEGATED_CONJECTURE) {
    if(!u->inference().hasNext(iit)) {
      Color uCol;
      if(u->isClause()) {
	uCol=static_cast<Clause*>(u)->color();
      } else if(!inputFormulaColors.find(u,uCol)){
	uCol=static_cast<FormulaUnit*>(u)->getColor();
	inputFormulaColors.insert(u,uCol);
      }
      if(uCol!=COLOR_TRANSPARENT) {
#if VDEBUG
	inputColor=static_cast<Color>(inputColor|uCol);
	ASS_NEQ(inputColor, COLOR_INVALID);
#else
	inputColor=uCol;
	break;
#endif
      }
    } else {
      while(u->inference().hasNext(iit)) {
        Unit* premUnit=u->inference().next(iit);
        units.push(premUnit);
      }
    }
  }

  if(inputColor!=COLOR_TRANSPARENT) {
    onSymbolElimination(inputColor, cl);
  }
}


}
