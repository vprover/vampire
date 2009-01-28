/**
 * @file TermIndex.cpp
 * Implements class TermIndex.
 */

#include "../Kernel/Clause.hpp"
#include "../Kernel/Term.hpp"
#include "../Kernel/Ordering.hpp"

#include "../Inferences/Superposition.hpp"

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
  int selCnt=c->selected();
  for(int i=0; i<selCnt; i++) {
    Literal* lit=(*c)[i];
    TermIterator rsti=Superposition::getRewritableSubtermIterator(lit);
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
  int selCnt=c->selected();
  for(int i=0; i<selCnt; i++) {
    Literal* lit=(*c)[i];
    TermIterator lhsi=Superposition::getLHSIterator(lit);
    while(lhsi.hasNext()) {
      if(adding) {
	_is->insert(lhsi.next(), lit, c);
      } else {
	_is->remove(lhsi.next(), lit, c);
      }
    }
  }
}
