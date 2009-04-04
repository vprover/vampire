/**
 * @file LiteralSubstitutionTree.cpp
 * Implements class LiteralSubstitutionTree.
 */

#include "../Lib/Environment.hpp"
#include "../Lib/Metaiterators.hpp"
#include "../Kernel/Signature.hpp"
#include "../Kernel/Term.hpp"

#include "LiteralSubstitutionTree.hpp"

namespace Indexing
{

LiteralSubstitutionTree::LiteralSubstitutionTree()
: SubstitutionTree(2*env.signature->predicates())
{
}

void LiteralSubstitutionTree::insert(Literal* lit, Clause* cls)
{
  CALL("LiteralSubstitutionTree::insert");
  handleLiteral(lit,cls,true);
}

void LiteralSubstitutionTree::remove(Literal* lit, Clause* cls)
{
  CALL("LiteralSubstitutionTree::remove");
  handleLiteral(lit,cls,false);
}

void LiteralSubstitutionTree::handleLiteral(Literal* lit, Clause* cls, bool insert)
{
  CALL("LiteralSubstitutionTree::handleLiteral");

  Renaming normalizer;
  normalizer.normalizeVariables(lit);
  Literal* normLit=normalizer.apply(lit);

  BindingMap svBindings;
  getBindings(normLit, svBindings);
  if(insert) {
    SubstitutionTree::insert(&_nodes[getRootNodeIndex(normLit)], svBindings, LeafData(cls, lit));
  } else {
    SubstitutionTree::remove(&_nodes[getRootNodeIndex(normLit)], svBindings, LeafData(cls, lit));
  }
}

SLQueryResultIterator LiteralSubstitutionTree::getUnifications(Literal* lit,
	  bool complementary, bool retrieveSubstitutions)
{
  CALL("LiteralSubstitutionTree::getUnifications");
  return getResultIterator<UnificationsIterator>(lit,
	  complementary, retrieveSubstitutions);
}

SLQueryResultIterator LiteralSubstitutionTree::getGeneralizations(Literal* lit,
	  bool complementary, bool retrieveSubstitutions)
{
  CALL("LiteralSubstitutionTree::getGeneralizations");
  return getResultIterator<FastGeneralizationsIterator>(lit,
	  complementary, retrieveSubstitutions);
}

SLQueryResultIterator LiteralSubstitutionTree::getInstances(Literal* lit,
	  bool complementary, bool retrieveSubstitutions)
{
  CALL("LiteralSubstitutionTree::getInstances");
  return getResultIterator<InstancesIterator>(lit,
	  complementary, retrieveSubstitutions);
}


struct LiteralSubstitutionTree::SLQueryResultFunctor
{
  DECL_RETURN_TYPE(SLQueryResult);
  OWN_RETURN_TYPE operator() (const QueryResult& qr) {
    return SLQueryResult(qr.first->literal, qr.first->clause, qr.second);
  }
};

struct LiteralSubstitutionTree::LDToSLQueryResultFn
{
  DECL_RETURN_TYPE(SLQueryResult);
  OWN_RETURN_TYPE operator() (const LeafData& ld) {
    return SLQueryResult(ld.literal, ld.clause);
  }
};

struct LiteralSubstitutionTree::LeafToLDIteratorFn
{
  DECL_RETURN_TYPE(LDIterator);
  OWN_RETURN_TYPE operator() (Leaf* l) {
    return l->allChildren();
  }
};

struct LiteralSubstitutionTree::PropositionalLDToSLQueryResultWithSubstFn
{
  PropositionalLDToSLQueryResultWithSubstFn()
  {
    _subst=ResultSubstitutionSP (new IdentitySubstitution());
  }
  DECL_RETURN_TYPE(SLQueryResult);
  OWN_RETURN_TYPE operator() (const LeafData& ld) {
    ASS_EQ(ld.literal->arity(),0);
    return SLQueryResult(ld.literal, ld.clause, _subst);
  }
private:
  ResultSubstitutionSP _subst;
};


SLQueryResultIterator LiteralSubstitutionTree::getAll()
{
  CALL("LiteralSubstitutionTree::getAll");

  return pvi( getMappingIterator(
      getMapAndFlattenIterator(
	  vi( new LeafIterator(this) ),
	  LeafToLDIteratorFn()),
      LDToSLQueryResultFn()) ) ;
}

template<class Iterator>
SLQueryResultIterator LiteralSubstitutionTree::getResultIterator(Literal* lit,
	  bool complementary, bool retrieveSubstitutions)
{
  CALL("LiteralSubstitutionTree::getResultIterator");

  Node* root=_nodes[getRootNodeIndex(lit, complementary)];

  if(root==0) {
    return SLQueryResultIterator::getEmpty();
  }
  if(root->isLeaf()) {
    LDIterator ldit=static_cast<Leaf*>(root)->allChildren();
    if(retrieveSubstitutions) {
      return pvi( getMappingIterator(ldit,PropositionalLDToSLQueryResultWithSubstFn()) );
    } else {
      return pvi( getMappingIterator(ldit,LDToSLQueryResultFn()) );
    }
  }

  if(lit->commutative()) {
    VirtualIterator<QueryResult> qrit1=vi(
  	    new Iterator(this, root, lit, retrieveSubstitutions) );
    VirtualIterator<QueryResult> qrit2=vi(
  	    new Iterator(this, root, lit, retrieveSubstitutions, true) );
    return pvi( getMappingIterator(
	    getConcatenatedIterator(qrit1,qrit2), SLQueryResultFunctor()) );
  } else {
    VirtualIterator<QueryResult> qrit=VirtualIterator<QueryResult>(
  	    new Iterator(this, root, lit, retrieveSubstitutions) );
    return pvi( getMappingIterator(qrit, SLQueryResultFunctor()) );
  }
}

unsigned LiteralSubstitutionTree::getRootNodeIndex(Literal* t, bool complementary)
{
  if(complementary) {
    return t->complementaryHeader();
  } else {
    return t->header();
  }
}



}
