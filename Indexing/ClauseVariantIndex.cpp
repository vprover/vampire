/**
 * @file ClauseVariantIndex.cpp
 * Implements class ClauseVariantIndex.
 */

#include "../Lib/List.hpp"
#include "../Lib/Metaiterators.hpp"
#include "../Lib/SmartPtr.hpp"
#include "../Kernel/Clause.hpp"
#include "../Kernel/MLMatcher.hpp"
#include "../Kernel/Term.hpp"

#include "LiteralMiniIndex.hpp"
#include "LiteralSubstitutionTree.hpp"

#include "ClauseVariantIndex.hpp"

//string treeStr;

namespace Indexing
{

using namespace Lib;
using namespace Kernel;

ClauseVariantIndex::~ClauseVariantIndex()
{
  unsigned streeArrSz=_strees.size();
  for(unsigned i=0;i<streeArrSz;i++) {
    if(_strees[i]!=0) {
      delete _strees[i];
    }
  }
}

void ClauseVariantIndex::insert(Clause* cl)
{
  unsigned clen=cl->length();
  if(!_strees[clen]) {
    _strees[clen]=new LiteralSubstitutionTree();
//    cout<<"Created index for len "<<clen<<": "<<_strees[clen]<<endl;
  }
  Literal* mainLit=getMainLiteral(cl->literals(), clen);
  _strees[clen]->insert(mainLit, cl);
//  cout<<"Stored "<<cl->length()<<" into "<<_strees[clen]<<endl;
}

Literal* ClauseVariantIndex::getMainLiteral(Literal** lits, unsigned length)
{
  Literal* best=lits[0];
  unsigned bestVal=best->weight()-best->getDistinctVars();
  for(unsigned i=1;i<length;i++) {
    Literal* curr=lits[i];
    unsigned currVal=curr->weight()-curr->getDistinctVars();
    if(currVal>bestVal || (currVal==bestVal && curr>best) ) {
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
    //Since we know that all mcl literals in alts array are variants
    //of their counterparts, it should be ok to use multiset matching in
    //here. (It'll be all rewritten after we have code trees, anyway.)
    fail=MLMatcher::canBeMatched(_lits,_length,mcl,alts.array(), 0, true);

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
  LiteralSubstitutionTree* index=_strees[length];
  if(!index) {
    return ClauseIterator::getEmpty();
  }

//  treeStr=index->toString();

  Literal* mainLit=getMainLiteral(lits, length);
  return pvi( getFilteredIterator(
	  getMappingIterator(
		  index->getVariants(mainLit, false, false),
		  SLResultToVariantClauseFn(lits, length)),
	  NonzeroFn()) );
}


}
