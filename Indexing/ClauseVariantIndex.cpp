/**
 * @file ClauseVariantIndex.cpp
 * Implements class ClauseVariantIndex.
 */

#include "Lib/List.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/SmartPtr.hpp"
#include "Lib/TimeCounter.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/LiteralComparators.hpp"
#include "Kernel/MLVariant.hpp"
#include "Kernel/Term.hpp"

#include "LiteralMiniIndex.hpp"
#include "LiteralSubstitutionTree.hpp"

#include "ClauseVariantIndex.hpp"

namespace Indexing
{

using namespace Lib;
using namespace Kernel;

ClauseVariantIndex::~ClauseVariantIndex()
{
  CALL("ClauseVariantIndex::~ClauseVariantIndex");

  unsigned streeArrSz=_strees.size();
  for(unsigned i=0;i<streeArrSz;i++) {
    if(_strees[i]!=0) {
      delete _strees[i];
    }
  }
}

void ClauseVariantIndex::insert(Clause* cl)
{
  CALL("ClauseVariantIndex::insert");

  unsigned clen=cl->length();

  if(cl->length()==0) {
    ClauseList::push(cl, _emptyClauses);
    return;
  }
  if(cl->length()==1 && (*cl)[0]->ground()) {
    Literal* lit=(*cl)[0];
    ClauseList** plist;
    _groundUnits.getValuePtr(lit, plist,0);
    ClauseList::push(cl, *plist);
    return;
  }

  if(!_strees[clen]) {
    _strees[clen]=new LiteralSubstitutionTree();
  }
  Literal* mainLit=getMainLiteral(cl->literals(), clen);
  _strees[clen]->insert(mainLit, cl);
}

Literal* ClauseVariantIndex::getMainLiteral(Literal** lits, unsigned length)
{
  CALL("ClauseVariantIndex::getMainLiteral");
  ASS_G(length,0);

  static LiteralComparators::NormalizedLinearComparatorByWeight<> comp;

  Literal* best=lits[0];
  unsigned bestVal=best->weight()-best->getDistinctVars();
  for(unsigned i=1;i<length;i++) {
    Literal* curr=lits[i];
    unsigned currVal=curr->weight()-curr->getDistinctVars();
    if(currVal>bestVal || (currVal==bestVal && comp.compare(curr, best)==GREATER ) ) {
      best=curr;
      bestVal=currVal;
    }
  }
  return best;
}

class ClauseVariantIndex::SLResultToVariantClauseFn
{
public:
  SLResultToVariantClauseFn(Literal** lits, unsigned length)
  : _lits(lits), _length(length), _queryIndex(new LiteralMiniIndex(lits, length))
  {
  }
  ~SLResultToVariantClauseFn()
  {
  }

  DECL_RETURN_TYPE(Clause*);

  OWN_RETURN_TYPE operator()(SLQueryResult res)
  {
    bool fail=false;

    static DArray<LiteralList*> alts(32);
    alts.init(_length, 0);

    Clause* mcl=res.clause;
    ASSERT_VALID(*mcl);
    ASS_EQ(mcl->length(),_length);

    for(unsigned i=0;i<_length;i++) {
      LiteralMiniIndex::VariantIterator vit(*_queryIndex, (*mcl)[i], false);
      if(!vit.hasNext()) {
	fail=true;
	goto fin;
      }
      while(vit.hasNext()) {
	Literal* qVarLit=vit.next();
	unsigned qVarLitIndex=_length;
	for(unsigned j=0;j<_length;j++) {
	  if(qVarLit==_lits[j]) {
	    qVarLitIndex=j;
	    break;
	  }
	}
	LiteralList::push((*mcl)[i], alts[qVarLitIndex]);
      }
    }
    for(unsigned i=0;i<_length;i++) {
      if(!alts[i]) {
	fail=true;
	goto fin;
      }
    }

    fail=!MLVariant::isVariant(_lits,mcl,alts.array());

  fin:
    for(unsigned i=0;i<_length;i++) {
      alts[i]->destroy();
    }

    if(fail) {
      return 0;
    } else {
      return mcl;
    }
  }

private:
  Literal** _lits;
  unsigned _length;
  SmartPtr<LiteralMiniIndex> _queryIndex;
};

ClauseIterator ClauseVariantIndex::retrieveVariants(Literal** lits, unsigned length)
{
  CALL("ClauseVariantIndex::retrieveVariants");

  if(length==0) {
    return pvi( ClauseList::Iterator(_emptyClauses) );
  }
  if(length==1 && lits[0]->ground()) {
    ClauseList* lst;
    if(_groundUnits.find(lits[0], lst)) {
      ASS(lst);
      return pvi( ClauseList::Iterator(lst) );
    }
    else {
      return ClauseIterator::getEmpty();
    }
  }

  LiteralSubstitutionTree* index=_strees[length];
  if(!index) {
    return ClauseIterator::getEmpty();
  }

  Literal* mainLit=getMainLiteral(lits, length);
  return pvi( getFilteredIterator(
	  getMappingIterator(
		  index->getVariants(mainLit, false, false),
		  SLResultToVariantClauseFn(lits, length)),
	  NonzeroFn()) );
}


}
