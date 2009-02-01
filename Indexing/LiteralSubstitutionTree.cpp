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
  Renaming::normalizeVariables(lit,normalizer);
  Literal* normLit=normalizer.apply(lit);

  BindingQueue bq;
  getBindings(normLit, bq);
  if(insert) {
    SubstitutionTree::insert(_nodes+getRootNodeIndex(normLit), bq, LeafData(cls, lit));
  } else {
    SubstitutionTree::remove(_nodes+getRootNodeIndex(normLit), bq, LeafData(cls, lit));
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
  if(retrieveSubstitutions) {
    return getResultIterator<GeneralizationsIterator>(lit,
	complementary, retrieveSubstitutions);
  } else {
    return getResultIterator<FastGeneralizationsIterator>(lit,
	complementary, retrieveSubstitutions);
  }
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

template<class Iterator>
SLQueryResultIterator LiteralSubstitutionTree::getResultIterator(Literal* lit,
	  bool complementary, bool retrieveSubstitutions)
{
  CALL("LiteralSubstitutionTree::getResultIterator");

  if(lit->commutative()) {
    Node* root=_nodes[getRootNodeIndex(lit, complementary)];
    VirtualIterator<QueryResult> qrit1=vi(
  	    new Iterator(root, lit, retrieveSubstitutions) );
    VirtualIterator<QueryResult> qrit2=vi(
  	    new Iterator(root, lit, retrieveSubstitutions, true) );
    return pvi( getMappingIterator(
	    getConcatenatedIterator(qrit1,qrit2), SLQueryResultFunctor()) );
  } else {
    Node* root=_nodes[getRootNodeIndex(lit, complementary)];
    VirtualIterator<QueryResult> qrit=VirtualIterator<QueryResult>(
  	    new Iterator(root, lit, retrieveSubstitutions) );
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
