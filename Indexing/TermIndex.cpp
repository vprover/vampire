
/*
 * File TermIndex.cpp.
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
 * @file TermIndex.cpp
 * Implements class TermIndex.
 */

#include "Lib/DHSet.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/HOSortHelper.hpp"

#include "Shell/LambdaElimination.hpp"

#include "TermIndexingStructure.hpp"
#include "TermIndex.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Inferences;
using namespace Indexing;

TermIndex::~TermIndex()
{
  delete _is;
}

TermQueryResultIterator TermIndex::getUnifications(TermList t,
	  bool retrieveSubstitutions)
{
  return _is->getUnifications(t, retrieveSubstitutions);
}

TermQueryResultIterator TermIndex::getUnificationsWithConstraints(TermList t,
          bool retrieveSubstitutions)
{
  return _is->getUnificationsWithConstraints(t, retrieveSubstitutions);
}

TermQueryResultIterator TermIndex::getGeneralizations(TermList t,
	  bool retrieveSubstitutions)
{
  return _is->getGeneralizations(t, retrieveSubstitutions);
}

TermQueryResultIterator TermIndex::getInstances(TermList t,
	  bool retrieveSubstitutions)
{
  return _is->getInstances(t, retrieveSubstitutions);
}


void ExtendedNarrowingIndex::populateIndex()
{
  CALL("ExtendedNarrowingIndex::populateIndex");
 
  typedef LambdaElimination LE; 
  typedef HOSortHelper HSH;
 
  TermList andTerm, orTerm, notTerm, impTerm, iffTerm, xorTerm;
  
  bool added;
  unsigned boolS = Sorts::SRT_BOOL; 
  unsigned boolToBoolS = env.sorts->addFunctionSort(Sorts::SRT_BOOL, Sorts::SRT_BOOL);
  unsigned boolToBoolToBools = env.sorts->addFunctionSort(Sorts::SRT_BOOL, boolToBoolS);
  
  Stack<unsigned> argSorts;
  Stack<TermList> args;
  
  argSorts.push(boolS);
  argSorts.push(boolS);
  
  args.push(TermList(1, false));
  args.push(TermList(0, false));
  
  TermList andConstant = LE::addHolConstant("vAND", boolToBoolToBools, added, Signature::Symbol::AND);
  TermList orConstant  = LE::addHolConstant("vOR",  boolToBoolToBools, added, Signature::Symbol::OR);
  TermList impConstant = LE::addHolConstant("vIMP", boolToBoolToBools, added, Signature::Symbol::IMP);
 // TermList iffConstant = LE::addHolConstant("vIFF", boolToBoolToBools, added, Signature::Symbol::IFF);
  //TermList xorConstant = LE::addHolConstant("vXOR", boolToBoolToBools, added, Signature::Symbol::XOR);
  TermList notConstant = LE::addHolConstant("vNOT", boolToBoolS, added, Signature::Symbol::NOT);
  
  andTerm = TermList(HSH::createAppifiedTerm(andConstant, boolToBoolToBools, argSorts, args));
  orTerm  = TermList(HSH::createAppifiedTerm(orConstant, boolToBoolToBools, argSorts, args));
  impTerm = TermList(HSH::createAppifiedTerm(impConstant, boolToBoolToBools, argSorts, args));
  //iffTerm = TermList(HSH::createAppifiedTerm(iffConstant, boolToBoolToBools, argSorts, args));
  //xorTerm = TermList(HSH::createAppifiedTerm(xorConstant, boolToBoolToBools, argSorts, args));
  args.pop(); argSorts.pop();
  notTerm = TermList(HSH::createAppifiedTerm(notConstant, boolToBoolS, argSorts, args));
 
  _is->insert(andTerm, 0, 0);
  _is->insert(orTerm, 0, 0);
  _is->insert(impTerm, 0, 0);
  //_is->insert(iffTerm, 0, 0);
  //_is->insert(xorTerm, 0, 0);
  _is->insert(notTerm, 0, 0);  
}


void SuperpositionSubtermIndex::handleClause(Clause* c, bool adding)
{
  CALL("SuperpositionSubtermIndex::handleClause");

  TimeCounter tc(TC_BACKWARD_SUPERPOSITION_INDEX_MAINTENANCE);

  unsigned selCnt=c->numSelected();
  for (unsigned i=0; i<selCnt; i++) {
    Literal* lit=(*c)[i];
    TermIterator rsti=EqHelper::getRewritableSubtermIterator(lit,_ord);
    while (rsti.hasNext()) {
      if (adding) {
	_is->insert(rsti.next(), lit, c);
      }
      else {
	_is->remove(rsti.next(), lit, c);
      }
    }
  }
}

void SuperpositionLHSIndex::handleClause(Clause* c, bool adding)
{
  CALL("SuperpositionLHSIndex::handleClause");

  TimeCounter tc(TC_FORWARD_SUPERPOSITION_INDEX_MAINTENANCE);

  unsigned selCnt=c->numSelected();
  for (unsigned i=0; i<selCnt; i++) {
    Literal* lit=(*c)[i];
    TermIterator lhsi=EqHelper::getSuperpositionLHSIterator(lit, _ord, _opt);
    while (lhsi.hasNext()) {
      TermList lhs=lhsi.next();
      if (adding) {
	_is->insert(lhs, lit, c);
      }
      else {
	_is->remove(lhs, lit, c);
      }
    }
  }
}

void DemodulationSubtermIndex::handleClause(Clause* c, bool adding)
{
  CALL("DemodulationSubtermIndex::handleClause");

  TimeCounter tc(TC_BACKWARD_DEMODULATION_INDEX_MAINTENANCE);

  static DHSet<TermList> inserted;

  unsigned cLen=c->length();
  for (unsigned i=0; i<cLen; i++) {
    inserted.reset();
    Literal* lit=(*c)[i];
    NonVariableIterator nvi(lit);
    while (nvi.hasNext()) {
      TermList t=nvi.next();
      if (!inserted.insert(t)) {
	//It is enough to insert a term only once per clause.
	//Also, once we know term was inserted, we know that all its
	//subterms were inserted as well, so we can skip them.
	nvi.right();
	continue;
      }
      if (adding) {
	_is->insert(t, lit, c);
      }
      else {
	_is->remove(t, lit, c);
      }
    }
  }
}


void DemodulationLHSIndex::handleClause(Clause* c, bool adding)
{
  CALL("DemodulationLHSIndex::handleClause");

  if (c->length()!=1) {
    return;
  }

  TimeCounter tc(TC_FORWARD_DEMODULATION_INDEX_MAINTENANCE);

  Literal* lit=(*c)[0];
  TermIterator lhsi=EqHelper::getDemodulationLHSIterator(lit, true, _ord, _opt);
  while (lhsi.hasNext()) {
    if (adding) {
      _is->insert(lhsi.next(), lit, c);
    }
    else {
      _is->remove(lhsi.next(), lit, c);
    }
  }
}
