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

class ClauseVariantIndex::ResultClauseToVariantClauseFn
{
public:
  ResultClauseToVariantClauseFn(Literal* const * lits, unsigned length)
  : _lits(lits), _length(length), _queryIndex(new LiteralMiniIndex(lits, length))
  {
  }
  ~ResultClauseToVariantClauseFn()
  {
  }


  Clause* operator()(Clause* mcl)
  {
    bool fail=false;

    ASSERT_VALID(*mcl);
    if (mcl->length() != _length) {
      return 0;
    }

    static DArray<LiteralList*> alts(32);
    alts.init(_length, 0);

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
      LiteralList::destroy(alts[i]);
    }

    if(fail) {
      return 0;
    } else {
      return mcl;
    }
  }

private:
  Literal* const * _lits;
  unsigned _length;
  SmartPtr<LiteralMiniIndex> _queryIndex;
};

class SubstitutionTreeClauseVariantIndex::SLQueryResultToClauseFn
{
public:

  Clause* operator()(SLQueryResult res) {
    return res.clause;
  }
};

ClauseIterator SubstitutionTreeClauseVariantIndex::retrieveVariants(Literal* const * lits, unsigned length)
{
  CALL("SubstitutionTreeClauseVariantIndex::retrieveVariants/2");

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
      getCompositionFn(ResultClauseToVariantClauseFn(lits, length),SLQueryResultToClauseFn())),
    NonzeroFn()) );
}

//-------------------//-------------------//-------------------//-------------------
//-------------------//-------------------//-------------------//-------------------

SubstitutionTreeClauseVariantIndex::~SubstitutionTreeClauseVariantIndex()
{
  CALL("SubstitutionTreeClauseVariantIndex::~SubstitutionTreeClauseVariantIndex");

  unsigned streeArrSz=_strees.size();
  for(unsigned i=0;i<streeArrSz;i++) {
    if(_strees[i]!=0) {
      delete _strees[i];
    }
  }

  ClauseList::destroy(_emptyClauses);

  DHMap<Literal*, ClauseList*>::Iterator it(_groundUnits);
  while (it.hasNext()) {
    ClauseList::destroy(it.next());
  }
}

/**
 * Inserts a new Clause
 *
 */
void SubstitutionTreeClauseVariantIndex::insert(Clause* cl)
{
  CALL("SubstitutionTreeClauseVariantIndex::insert");

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

Literal* SubstitutionTreeClauseVariantIndex::getMainLiteral(Literal* const * lits, unsigned length)
{
  CALL("SubstitutionTreeClauseVariantIndex::getMainLiteral");
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

//-------------------//-------------------//-------------------//-------------------
//-------------------//-------------------//-------------------//-------------------

HashingClauseVariantIndex::~HashingClauseVariantIndex()
{
  CALL("HashingClauseVariantIndex::~HashingClauseVariantIndex");

  /*
  unsigned max = 0;
  ClauseList* maxval = 0;
  */

  DHMap<unsigned, ClauseList*>::Iterator iit(_entries);
  while(iit.hasNext()){
    ClauseList* lst = iit.next();

//    unsigned len = lst->length();
//
//    if (len > max) {
//      max = len;
//      maxval->destroy();
//      maxval = lst;
//    } else {
    ClauseList::destroy(lst);
//    }
  }

  /*
  cout << "max bucket of size " << max << endl;
  ClauseList::Iterator it(maxval);
  while (it.hasNext()) {
    Clause* cl = it.next();
    cout << cl->toString() << endl;
  }

  maxval->destroy();
  */
}

void HashingClauseVariantIndex::insert(Clause* cl)
{
  CALL("HashingClauseVariantIndex::insert");

  TimeCounter tc( TC_HCVI_INSERT);

  // static unsigned insertions = 0;

  //cout << "insert " << cl->toString() << endl;

  unsigned h = computeHash(cl->literals(),cl->length());

  //cout << "hashed to " << h << endl;

  ClauseList** lst;
  _entries.getValuePtr(h,lst);
  ClauseList::push(cl, *lst);

  // cout << "bucket of size " << (*lst)->length() << endl;
  // cout << _entries.size() << "buckets after " << ++insertions << " insertions" << endl;
}

ClauseIterator HashingClauseVariantIndex::retrieveVariants(Literal* const * lits, unsigned length)
{
  CALL("HashingClauseVariantIndex::retrieveVariants/2");

  TimeCounter tc( TC_HCVI_RETRIEVE );

  unsigned h = computeHash(lits,length);

  //cout << "hashed to " << h << endl;

  ClauseList* lst;
  if (_entries.find(h,lst)) {
    //cout << "found this long list: " << lst->length() << endl;

    return pvi( getFilteredIterator(
        getMappingIterator(
          ClauseList::Iterator(lst),
          ResultClauseToVariantClauseFn(lits, length)),
        NonzeroFn()) );
  } else {
    return ClauseIterator::getEmpty();
  }
}

struct HashingClauseVariantIndex::VariableIgnoringComparator {
  Literal* const * _lits;
  VariableIgnoringComparator(Literal* const * lits) : _lits(lits) {}

  static Comparison disagreement(Term* t1,Term* t2)
  {
    CALL("HashingClauseVariantIndex::VariableIgnoringComparator::disagreement");

    //now get just some total deterministic order while ignoring variables
    static DisagreementSetIterator dsit;
    dsit.reset(t1, t2, false);
    while(dsit.hasNext()) {
      pair<TermList, TermList> dis=dsit.next();
      if(dis.first.isTerm()) {
        if(dis.second.isTerm()) {
          ASS_NEQ(dis.first.term()->functor(), dis.second.term()->functor());
          return Int::compare(dis.first.term()->functor(), dis.second.term()->functor());
        }
        return GREATER;
      }
      if(dis.second.isTerm()) {
        return LESS;
      }
      // ignore disagreement on variables
    }
    //they're equal up to ignoring variables
    return EQUAL;
  }

  static Comparison compare(TermList* tl1, TermList* tl2)
  {
    CALL("HashingClauseVariantIndex::VariableIgnoringComparator::compare(Termlist*,Termlist*)");

    if(!tl1->isTerm()) {
      if(!tl2->isTerm()) {
        return EQUAL;
      }
      return LESS;
    }

    if(!tl2->isTerm()) {
      return GREATER;
    }

    Term* t1 = tl1->term();
    Term* t2 = tl2->term();

    if(t1->weight()!=t2->weight()) {
      // number of general symbol occurrences
      return Int::compare(t1->weight(),t2->weight());
    }

    if(t1->vars()!=t2->vars()) {
      // number of variable occurrences
      return Int::compare(t1->vars(),t2->vars());
    }

    if (t1->ground()) {
      ASS(t2->ground());
      return Int::compare(t1->getId(),t2->getId());
    }

    if(t1->functor()!=t2->functor()) {
      return Int::compare(t1->functor(),t2->functor());
    }

    return disagreement(t1,t2);
  }

  static Comparison compare(Literal* l1, Literal* l2)
  {
    CALL("HashingClauseVariantIndex::VariableIgnoringComparator::compare(Literal*,Literal*)");

    if(l1->weight()!=l2->weight()) {
      // number of general symbol occurrences
      return Int::compare(l1->weight(),l2->weight());
    }

    if(l1->vars()!=l2->vars()) {
      // number of variable occurrences
      return Int::compare(l1->vars(),l2->vars());
    }

    if (l1->ground()) {
      ASS(l2->ground());
      return Int::compare(l1->getId(),l2->getId());
    }

    if(l1->header()!=l2->header()) {
      // functor and polarity
      return Int::compare(l1->header(),l2->header());
    }

    if(l1->isEquality()) {
      ASS(l2->isEquality());

      TermList* l1l = l1->nthArgument(0);
      TermList* l1r = l1->nthArgument(1);
      if (compare(l1l,l1r) == LESS) {
        swap(l1l,l1r);
      }

      TermList* l2l = l2->nthArgument(0);
      TermList* l2r = l2->nthArgument(1);
      if (compare(l2l,l2r) == LESS) {
        swap(l2l,l2r);
      }

      Comparison res = compare(l1l,l2l);
      if (res != EQUAL) {
        return res;
      }
      return compare(l1r,l2r);
    }

    return disagreement(l1,l2);
  }

  /**
   * A total ordering stable under variable substitutions.
   */
  bool operator()(unsigned a, unsigned b) {
    CALL("HashingClauseVariantIndex::VariableIgnoringComparator::operator()");

    // cout << "a = " << a << " lits[a]= " << _lits[a] << endl;
    // cout << "b = " << b << " lits[b]= " << _lits[b] << endl;

    Literal* la = _lits[a];
    Literal* lb = _lits[b];

    // cout << "a " << la->toString() << endl;
    // cout << "b " << lb->toString() << endl;

    return (compare(la,lb) == LESS);
  }
};

unsigned HashingClauseVariantIndex::computeHashAndCountVariables(TermList* ptl, VarCounts& varCnts, unsigned hash_begin) {
  CALL("HashingClauseVariantIndex::computeHashAndCountVariables(Term*, ...)");

  if (ptl->isVar()) {
    return computeHashAndCountVariables(ptl->var(),varCnts,hash_begin);
  }

  Term* t = ptl->term();

  if (t->ground()) {
    // no variables to count

    // just hash the pointer
    return Hash::hash((const unsigned char*)&t,sizeof(t),hash_begin);
  }

  unsigned hash = termFunctorHash(t,hash_begin);

  SubtermIterator sti(t);
  while(sti.hasNext()) {
    TermList tl = sti.next();

    if (tl.isVar()) {
      hash = computeHashAndCountVariables(tl.var(),varCnts,hash);
    } else {
      hash = termFunctorHash(tl.term(),hash);
    }
  }

  return hash;
}

unsigned HashingClauseVariantIndex::computeHashAndCountVariables(Literal* l, VarCounts& varCnts, unsigned hash_begin) {
  CALL("HashingClauseVariantIndex::computeHashAndCountVariables(Literal*, ...)");

  //cout << "Literal " << l->toString() << endl;

  if (l->ground()) {
    // no variables to count

    // just hash the pointer
    return Hash::hash((const unsigned char*)&l,sizeof(l),hash_begin);
  }

  //cout << "will hash header " << header << endl;

  unsigned header = l->header();

  // hashes the predicate symbol and the polarity
  unsigned hash = Hash::hash((const unsigned char*)&header,sizeof(header),hash_begin);

  if(l->isEquality()) {
    TermList* ll = l->nthArgument(0);
    TermList* lr = l->nthArgument(1);
    if (VariableIgnoringComparator::compare(ll,lr) == LESS) {
      swap(ll,lr);
    }

    hash = computeHashAndCountVariables(ll,varCnts,hash);
    hash = computeHashAndCountVariables(lr,varCnts,hash);
  } else {
    for(TermList* arg=l->args(); arg->isNonEmpty(); arg=arg->next()) {
      hash = computeHashAndCountVariables(arg,varCnts,hash);
    }
  }

  return hash;
}

unsigned HashingClauseVariantIndex::computeHash(Literal* const * lits, unsigned length)
{
  CALL("HashingClauseVariantIndex::computeHash");

  // cout << "length " <<  length << endl;

  TimeCounter tc( TC_HCVI_COMPUTE_HASH );

  static Stack<unsigned> litOrder;
  litOrder.reset();
  litOrder.loadFromIterator(getRangeIterator(0u,length));

  std::sort(litOrder.begin(), litOrder.end(), VariableIgnoringComparator(lits));

  static VarCounts varCnts;
  varCnts.reset();

  unsigned hash = 2166136261u;
  for(unsigned i=0; i<length; i++) {
    unsigned li = litOrder[i];
    hash = computeHashAndCountVariables(lits[li],varCnts,hash);
  }

  if (varCnts.size() > 0) {
    static Stack<unsigned char> varCntHistogram;
    varCntHistogram.reset();
    VarCounts::Iterator it(varCnts);
    while (it.hasNext()) {
      varCntHistogram.push(it.next());
    }

    std::sort(varCntHistogram.begin(),varCntHistogram.end());
    hash = Hash::hash((const unsigned char*)varCntHistogram.begin(),varCntHistogram.size(),hash);
  }

  return hash;
}


}
