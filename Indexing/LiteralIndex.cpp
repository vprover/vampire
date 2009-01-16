/**
 * @file LiteralIndex.cpp
 * Implements class LiteralIndex.
 */

#include "../Kernel/Clause.hpp"

#include "LiteralIndexingStructure.hpp"

#include "LiteralIndex.hpp"

using namespace Kernel;
using namespace Indexing;

LiteralIndex::~LiteralIndex()
{
  delete _is;
}

SLQueryResultIterator LiteralIndex::getUnifications(Literal* lit,
	  bool complementary, bool retrieveSubstitutions)
{
  return _is->getUnifications(lit, complementary, retrieveSubstitutions);
}

SLQueryResultIterator LiteralIndex::getGeneralizations(Literal* lit,
	  bool complementary, bool retrieveSubstitutions)
{
  return _is->getGeneralizations(lit, complementary, retrieveSubstitutions);
}

SLQueryResultIterator LiteralIndex::getInstances(Literal* lit,
	  bool complementary, bool retrieveSubstitutions)
{
  return _is->getInstances(lit, complementary, retrieveSubstitutions);
}


void GeneratingLiteralIndex::onAddedToContainer(Clause* c)
{
  int selCnt=c->selected();
  for(int i=0; i<selCnt; i++) {
    _is->insert((*c)[i], c);
  }
}

void GeneratingLiteralIndex::onRemovedFromContainer(Clause* c)
{
  int selCnt=c->selected();
  for(int i=0; i<selCnt; i++) {
    _is->remove((*c)[i], c);
  }
}

void SimplifyingLiteralIndex::onAddedToContainer(Clause* c)
{
  unsigned clen=c->length();
  for(unsigned i=0; i<clen; i++) {
    _is->insert((*c)[i], c);
  }
}

void SimplifyingLiteralIndex::onRemovedFromContainer(Clause* c)
{
  unsigned clen=c->length();
  for(unsigned i=0; i<clen; i++) {
    _is->remove((*c)[i], c);
  }
}

void AtomicClauseSimplifyingLiteralIndex::onAddedToContainer(Clause* c)
{
  if(c->length()==1) {
    _is->insert((*c)[0], c);
  }
}

void AtomicClauseSimplifyingLiteralIndex::onRemovedFromContainer(Clause* c)
{
  if(c->length()==1) {
    _is->remove((*c)[0], c);
  }
}
