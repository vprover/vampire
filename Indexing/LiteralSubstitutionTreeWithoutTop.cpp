/**
 * @file LiteralSubstitutionTreeWithoutTop.cpp
 * Implements class LiteralSubstitutionTreeWithoutTop.
 */

#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/TimeCounter.hpp"

#include "Kernel/Matcher.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"

#include "LiteralSubstitutionTreeWithoutTop.hpp"

namespace Indexing
{

LiteralSubstitutionTreeWithoutTop::LiteralSubstitutionTreeWithoutTop()
: SubstitutionTree(0), _posRoot(0), _negRoot(0) // We will not be using _nodes, instead we will use _root
{
  _nextVar=1;
}

void LiteralSubstitutionTreeWithoutTop::insert(Literal* lit, Clause* cls)
{
  CALL("LiteralSubstitutionTreeWithoutTop::insert");
  handleLiteral(lit,cls,true);
}

void LiteralSubstitutionTreeWithoutTop::remove(Literal* lit, Clause* cls)
{
  CALL("LiteralSubstitutionTreeWithoutTop::remove");
  handleLiteral(lit,cls,false);
}

void LiteralSubstitutionTreeWithoutTop::handleLiteral(Literal* lit, Clause* cls, bool insert)
{
  CALL("LiteralSubstitutionTreeWithoutTop::handleLiteral");
  
  Literal* normLit=Renaming::normalize(lit);

  Node** _root = lit->polarity() ? &_posRoot : &_negRoot;

  BindingMap svBindings;
  svBindings.insert(0,TermList(normLit));
  if(insert) {
    SubstitutionTree::insert(_root, svBindings, LeafData(cls, lit));
  } else {
    SubstitutionTree::remove(_root, svBindings, LeafData(cls, lit));
  }

}

SLQueryResultIterator LiteralSubstitutionTreeWithoutTop::getUnifications(Literal* lit,
	  bool complementary, bool retrieveSubstitutions)
{
  CALL("LiteralSubstitutionTreeWithoutTop::getUnifications");
  return getResultIterator<UnificationsIterator>(lit,
	  complementary, retrieveSubstitutions);
}

SLQueryResultIterator LiteralSubstitutionTreeWithoutTop::getGeneralizations(Literal* lit,
	  bool complementary, bool retrieveSubstitutions)
{
  CALL("LiteralSubstitutionTreeWithoutTop::getGeneralizations");

  SLQueryResultIterator res=
//  getResultIterator<GeneralizationsIterator>(lit,
    getResultIterator<FastGeneralizationsIterator>(lit,
	  	  complementary, retrieveSubstitutions);
//  ASS_EQ(res.hasNext(), getResultIterator<GeneralizationsIterator>(lit,
//	  	  complementary, retrieveSubstitutions).hasNext());
  return res;
}

SLQueryResultIterator LiteralSubstitutionTreeWithoutTop::getInstances(Literal* lit,
	  bool complementary, bool retrieveSubstitutions)
{
  CALL("LiteralSubstitutionTreeWithoutTop::getInstances");

//  return getResultIterator<InstancesIterator>(lit, complementary, true);

  if(retrieveSubstitutions) {
#if VDEBUG
    NOT_IMPLEMENTED;
#endif
    return getResultIterator<InstancesIterator>(lit, complementary, true);
  }

  SLQueryResultIterator res=
//      getResultIterator<InstancesIterator>(lit,
      getResultIterator<FastInstancesIterator>(lit,
	  complementary, retrieveSubstitutions);
//  ASS_EQ(res.hasNext(), getResultIterator<InstancesIterator>(lit,
//      complementary, retrieveSubstitutions).hasNext());
  return res;
}

struct LiteralSubstitutionTreeWithoutTop::SLQueryResultFunctor
{
  DECL_RETURN_TYPE(SLQueryResult);
  OWN_RETURN_TYPE operator() (const QueryResult& qr) {
    return SLQueryResult(qr.first->literal, qr.first->clause, qr.second);
  }
};

struct LiteralSubstitutionTreeWithoutTop::LDToSLQueryResultFn
{
  DECL_RETURN_TYPE(SLQueryResult);
  OWN_RETURN_TYPE operator() (const LeafData& ld) {
    return SLQueryResult(ld.literal, ld.clause);
  }
};

#define QRS_QUERY_BANK 0
#define QRS_RESULT_BANK 1

struct LiteralSubstitutionTreeWithoutTop::LDToSLQueryResultWithSubstFn
{
  LDToSLQueryResultWithSubstFn()
  {
    _subst=RobSubstitutionSP(new RobSubstitution());
  }
  DECL_RETURN_TYPE(SLQueryResult);
  OWN_RETURN_TYPE operator() (const LeafData& ld) {
    return SLQueryResult(ld.literal, ld.clause,
	    ResultSubstitution::fromSubstitution(_subst.ptr(),
		    QRS_QUERY_BANK,QRS_RESULT_BANK));
  }
private:
  RobSubstitutionSP _subst;
};

struct LiteralSubstitutionTreeWithoutTop::UnifyingContext
{
  UnifyingContext(Literal* queryLit)
  : _queryLit(queryLit) {}
  bool enter(SLQueryResult qr)
  {
    ASS(qr.substitution);
    RobSubstitution* subst=qr.substitution->tryGetRobSubstitution();
    ASS(subst);

    //This code is used only during variant retrieval, so
    //literal commutativity doesn't need to concern us, as
    //we normalize the query literal, so the argument order
    //of commutative literals is always the right one.
    ALWAYS(subst->unifyArgs(_queryLit, QRS_QUERY_BANK, qr.literal, QRS_RESULT_BANK));

    return true;
  }
  void leave(SLQueryResult qr)
  {
    RobSubstitution* subst=qr.substitution->tryGetRobSubstitution();
    ASS(subst);
    subst->reset();
  }
private:
  Literal* _queryLit;
};


struct LiteralSubstitutionTreeWithoutTop::LeafToLDIteratorFn
{
  DECL_RETURN_TYPE(LDIterator);
  OWN_RETURN_TYPE operator() (Leaf* l) {
    return l->allChildren();
  }
};

struct LiteralSubstitutionTreeWithoutTop::PropositionalLDToSLQueryResultWithSubstFn
{
  PropositionalLDToSLQueryResultWithSubstFn()
  {
    _subst=ResultSubstitutionSP (new DisjunctQueryAndResultVariablesSubstitution()); 
  }
  DECL_RETURN_TYPE(SLQueryResult);
  OWN_RETURN_TYPE operator() (const LeafData& ld) {
    ASS_EQ(ld.literal->arity(),0);
    return SLQueryResult(ld.literal, ld.clause, _subst);
  }
private:
  ResultSubstitutionSP _subst;
};


SLQueryResultIterator LiteralSubstitutionTreeWithoutTop::getVariants(Literal* lit,
	  bool complementary, bool retrieveSubstitutions)
{
  CALL("LiteralSubstitutionTreeWithoutTop::getVariants");

  bool pol = complementary ? !lit->polarity() : lit->polarity();
  Node* _root = pol ? _posRoot : _negRoot; 

  if(_root==0) {
    return SLQueryResultIterator::getEmpty();
  }

  if(_root->isLeaf()) {
    LDIterator ldit=static_cast<Leaf*>(_root)->allChildren();
    if(retrieveSubstitutions) {
      // a single substitution will be used for all in ldit, but that's OK
      return pvi( getMappingIterator(ldit,PropositionalLDToSLQueryResultWithSubstFn()) );
    } else {
      return pvi( getMappingIterator(ldit,LDToSLQueryResultFn()) );
    }
  }

  Literal* normLit=Renaming::normalize(lit);

  BindingMap svBindings;
  svBindings.insert(0,TermList(normLit));
  Leaf* leaf = findLeaf(_root,svBindings);
  if(leaf==0) {
    return SLQueryResultIterator::getEmpty();
  }

  LDIterator ldit=leaf->allChildren();
  if(retrieveSubstitutions) {
    return pvi( getContextualIterator(
	    getMappingIterator(
		    ldit,
		    LDToSLQueryResultWithSubstFn()),
	    UnifyingContext(lit)) );
  } else {
    return pvi( getMappingIterator(ldit,LDToSLQueryResultFn()) );
  }
}

SLQueryResultIterator LiteralSubstitutionTreeWithoutTop::getAll()
{
  CALL("LiteralSubstitutionTreeWithoutTop::getAll");

  return pvi( getMappingIterator(
      getMapAndFlattenIterator(
	  vi( new LeafIterator(this) ),
	  LeafToLDIteratorFn()),
      LDToSLQueryResultFn()) ) ;
}


struct LiteralSubstitutionTreeWithoutTop::EqualitySortFilter
{
  DECL_RETURN_TYPE(bool);

  EqualitySortFilter(Literal* queryLit)
  : _queryEqSort(SortHelper::getEqualityArgumentSort(queryLit)) {}

  bool operator()(const SLQueryResult& res)
  {
    CALL("LiteralSubstitutionTreeWithoutTop::EqualitySortFilter::operator()");
    ASS(res.literal->isEquality());

    unsigned resSort = SortHelper::getEqualityArgumentSort(res.literal);
    return resSort==_queryEqSort;
  }
private:
  unsigned _queryEqSort;
};

template<class Iterator>
SLQueryResultIterator LiteralSubstitutionTreeWithoutTop::getResultIterator(Literal* lit,
	  bool complementary, bool retrieveSubstitutions)
{
  CALL("LiteralSubstitutionTreeWithoutTop::getResultIterator");

  bool pol = complementary ? !lit->polarity() : lit->polarity();
  Node* _root = pol ? _posRoot : _negRoot;

  if(_root==0) {
    return SLQueryResultIterator::getEmpty();
  }

  if(_root->isLeaf()) {
    LDIterator ldit=static_cast<Leaf*>(_root)->allChildren();
    if(retrieveSubstitutions) {
      // a single substitution will be used for all in ldit, but that's OK
      return pvi( getMappingIterator(ldit,PropositionalLDToSLQueryResultWithSubstFn()) );
    } else {
      return pvi( getMappingIterator(ldit,LDToSLQueryResultFn()) );
    }
  }

  if(lit->commutative()) {
    VirtualIterator<QueryResult> qrit1=vi(
  	    new Iterator(this, _root, lit, retrieveSubstitutions,false, true) );
    VirtualIterator<QueryResult> qrit2=vi(
  	    new Iterator(this, _root, lit, retrieveSubstitutions, true, true) );
    ASS(lit->isEquality());
    return pvi(
	getFilteredIterator(
	    getMappingIterator(
		getConcatenatedIterator(qrit1,qrit2), SLQueryResultFunctor()),
	    EqualitySortFilter(lit))
	);
  } else {
    VirtualIterator<QueryResult> qrit=VirtualIterator<QueryResult>(
  	    new Iterator(this, _root, lit, retrieveSubstitutions,false,true) );
    return pvi( getMappingIterator(qrit, SLQueryResultFunctor()) );
  }
}


}
