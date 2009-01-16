/**
 * @file TermIndex.cpp
 * Implements class TermIndex.
 */

#include "../Kernel/Clause.hpp"
#include "../Kernel/Term.hpp"
#include "../Kernel/Ordering.hpp"

#include "TermIndexingStructure.hpp"

#include "TermIndex.hpp"

using namespace Lib;
using namespace Kernel;
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


void SuperpositionSubtermIndex::onAddedToContainer(Clause* c)
{
  int selCnt=c->selected();
  for(int i=0; i<selCnt; i++) {
    Literal* lit=(*c)[i];
    Literal::NonVariableIterator nvi(lit);
    while(nvi.hasNext()) {
      _is->insert(nvi.next(), lit, c);
    }
  }
}

void SuperpositionSubtermIndex::onRemovedFromContainer(Clause* c)
{
  int selCnt=c->selected();
  for(int i=0; i<selCnt; i++) {
    Literal* lit=(*c)[i];
    Literal::NonVariableIterator nvi(lit);
    while(nvi.hasNext()) {
      _is->remove(nvi.next(), lit, c);
    }
  }
}


SuperpositionLHSIndex::SuperpositionLHSIndex(TermIndexingStructure* is)
: TermIndex(is), _ord(Ordering::instance())
{
}

void SuperpositionLHSIndex::onAddedToContainer(Clause* c)
{
  int selCnt=c->selected();
  for(int i=0; i<selCnt; i++) {
    Literal* lit=(*c)[i];
    if(!lit->isEquality() || lit->isNegative()) {
      continue;
    }
    TermList t1=*lit->nthArgument(0);
    TermList t2=*lit->nthArgument(1);
    switch(_ord->compare(t1,t2)) {
    case Ordering::EQUAL:
      //Same term shouldn't occur on both sides of an equality,
      //as trivial equalities get deleted by TautologyDeletionFSE.
      ASSERTION_VIOLATION;
      break;
    case Ordering::GREATER:
    case Ordering::GREATER_EQ:
      _is->insert(t1, lit, c);
      break;
    case Ordering::LESS:
    case Ordering::LESS_EQ:
      _is->insert(t2, lit, c);
      break;
    case Ordering::INCOMPARABLE:
      _is->insert(t1, lit, c);
      _is->insert(t2, lit, c);
      break;
    }
  }
}

void SuperpositionLHSIndex::onRemovedFromContainer(Clause* c)
{
  int selCnt=c->selected();
  for(int i=0; i<selCnt; i++) {
    Literal* lit=(*c)[i];
    if(!lit->isEquality() || lit->isNegative()) {
      continue;
    }
    TermList t1=*lit->nthArgument(0);
    TermList t2=*lit->nthArgument(1);
    switch(_ord->compare(t1,t2)) {
    case Ordering::EQUAL:
      //Same term shouldn't occur on both sides of an equality,
      //as trivial equalities get deleted by TautologyDeletionFSE.
      ASSERTION_VIOLATION;
      break;
    case Ordering::GREATER:
    case Ordering::GREATER_EQ:
      _is->insert(t1, lit, c);
      break;
    case Ordering::LESS:
    case Ordering::LESS_EQ:
      _is->insert(t2, lit, c);
      break;
    case Ordering::INCOMPARABLE:
      _is->insert(t1, lit, c);
      _is->insert(t2, lit, c);
      break;
    }
  }
}
