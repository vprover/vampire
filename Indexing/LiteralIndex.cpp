/**
 * @file LiteralIndex.cpp
 * Implements class LiteralIndex.
 */

#include "../Kernel/Clause.hpp"
#include "../Kernel/LiteralComparators.hpp"
#include "../Kernel/Ordering.hpp"

#include "LiteralIndexingStructure.hpp"
#include "LiteralSubstitutionTree.hpp"

#include "LiteralIndex.hpp"

namespace Indexing
{

using namespace Kernel;

LiteralIndex::~LiteralIndex()
{
  delete _is;
}

SLQueryResultIterator LiteralIndex::getAll()
{
  return _is->getAll();
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
  TimeCounter tc(TC_BINARY_RESOLUTION_INDEX_MAINTENANCE);

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
  TimeCounter tc(TC_BACKWARD_SUBSUMPTION_INDEX_MAINTENANCE);

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
  TimeCounter tc(TC_FORWARD_SUBSUMPTION_INDEX_MAINTENANCE);

  Literal* best=(*c)[0];
  unsigned bestVal=best->weight()-best->getDistinctVars();
  for(unsigned i=1;i<clen;i++) {
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
    TimeCounter tc(TC_SIMPLIFYING_UNIT_LITERAL_INDEX_MAINTENANCE);

    if(adding) {
      _is->insert((*c)[0], c);
    } else {
      _is->remove((*c)[0], c);
    }
  }
}


RewriteRuleIndex::RewriteRuleIndex(LiteralIndexingStructure* is)
: LiteralIndex(is)
{
  _partialIndex=new LiteralSubstitutionTree();
}

RewriteRuleIndex::~RewriteRuleIndex()
{
  delete _partialIndex;
}

void RewriteRuleIndex::handleClause(Clause* c, bool adding)
{
  if(c->length()!=2) {
    return;
  }
  //TODO: add time counter

  static LiteralComparators::NormalizedLinearComparatorByWeight<true> comparator;

  Comparison comp=comparator.compare((*c)[0], (*c)[1]);

  Literal* greater=
    ( comp==GREATER ) ? (*c)[0] :
    ( comp==LESS ) ? (*c)[1] : 0;

  if(greater) {
    SLQueryResultIterator vit=_partialIndex->getVariants(greater,true,false);
    while(vit.hasNext()) {
      SLQueryResult qr=vit.next();
      Clause* cl=qr.clause;
      //TODO: add variant check
      NOT_IMPLEMENTED;


      //we have found a counterpart

      //we can remove the literal from index of partial definitions
      _partialIndex->remove(qr.literal, qr.clause);

      Ordering::Result cmpRes=Ordering::instance()->compare((*c)[0],(*c)[1]);
      switch(cmpRes) {

      }
    }
    //there is no counterpart, so insert the clause into the partial index
    ALWAYS(vit.drop());
    _partialIndex->insert(greater, c);
  }
  else {
    //the two literals are variants of each other, so we don't need to wait
    //for the complementary clause
    if( (*c)[0]->polarity()==(*c)[1]->polarity() ) {
      _is->insert((*c)[0], c);
    }
    else {
      _is->insert((*c)[0], c);
      _is->insert((*c)[1], c);
    }
  }

}


}
