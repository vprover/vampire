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


void GeneratingLiteralIndex::handleClause(Clause* c, bool adding)
{
  int selCnt=c->selected();
  for(int i=0; i<selCnt; i++) {
    if(adding) {
      _is->insert((*c)[i], c);
    } else {
      _is->remove((*c)[i], c);
    }
  }
}

void SimplifyingLiteralIndex::handleClause(Clause* c, bool adding)
{
  unsigned clen=c->length();
  for(unsigned i=0; i<clen; i++) {
    if(adding) {
      _is->insert((*c)[i], c);
    } else {
      _is->remove((*c)[i], c);
    }
  }
}

void FwSubsSimplifyingLiteralIndex::handleClause(Clause* c, bool adding)
{
  unsigned clen=c->length();
  if(clen<2) {
    return;
  }
  Literal* best=(*c)[0];
  unsigned bestVal=best->weight()-best->getDistinctVars();
  for(unsigned i=0;i<clen;i++) {
    Literal* curr=(*c)[i];
    unsigned currVal=curr->weight()-curr->getDistinctVars();
    if(currVal>bestVal || (currVal==bestVal && curr>best) ) {
      best=curr;
      bestVal=currVal;
    }
  }
  if(adding) {
    _is->insert(best, c);
  } else {
    _is->remove(best, c);
  }
}

void UnitClauseSimplifyingLiteralIndex::handleClause(Clause* c, bool adding)
{
  if(c->length()==1) {
    if(adding) {
      _is->insert((*c)[0], c);
    } else {
      _is->remove((*c)[0], c);
    }
  }
}

