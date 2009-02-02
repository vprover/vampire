/**
 * @file TermIndex.cpp
 * Implements class TermIndex.
 */

#include "../Kernel/Clause.hpp"
#include "../Kernel/Term.hpp"
#include "../Kernel/Ordering.hpp"

#include "../Kernel/EqHelper.hpp"

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


void SuperpositionSubtermIndex::handleClause(Clause* c, bool adding)
{
  unsigned selCnt=c->selected();
  for(unsigned i=0; i<selCnt; i++) {
    Literal* lit=(*c)[i];
    TermIterator rsti=EqHelper::getRewritableSubtermIterator(lit);
    while(rsti.hasNext()) {
      if(adding) {
	_is->insert(rsti.next(), lit, c);
      } else {
	_is->remove(rsti.next(), lit, c);
      }
    }
  }
}


void SuperpositionLHSIndex::handleClause(Clause* c, bool adding)
{
  unsigned selCnt=c->selected();
  for(unsigned i=0; i<selCnt; i++) {
    Literal* lit=(*c)[i];
    TermIterator lhsi=EqHelper::getLHSIterator(lit);
    while(lhsi.hasNext()) {
      if(adding) {
	_is->insert(lhsi.next(), lit, c);
      } else {
	_is->remove(lhsi.next(), lit, c);
      }
    }
  }
}

void DemodulationSubtermIndex::handleClause(Clause* c, bool adding)
{
  unsigned cLen=c->length();
  for(unsigned i=0; i<cLen; i++) {
    Literal* lit=(*c)[i];
    Term::NonVariableIterator nvi(lit);
    while(nvi.hasNext()) {
      if(adding) {
	_is->insert(nvi.next(), lit, c);
      } else {
	_is->remove(nvi.next(), lit, c);
      }
    }
  }
}


void DemodulationLHSIndex::handleClause(Clause* c, bool adding)
{
  if(c->length()!=1) {
    return;
  }
  Literal* lit=(*c)[0];
  TermIterator lhsi=EqHelper::getLHSIterator(lit);
  while(lhsi.hasNext()) {
    if(adding) {
      _is->insert(lhsi.next(), lit, c);
    } else {
      _is->remove(lhsi.next(), lit, c);
    }
  }
}
