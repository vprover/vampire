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

  Renaming normalizer;
  Renaming::normalizeVariables(lit,normalizer);
  Literal* normLit=normalizer.apply(lit);

  BindingQueue bq;
  getBindings(normLit, bq);
  SubstitutionTree::insert(_nodes+getRootNodeIndex(lit), bq, LeafData(cls, lit));
}

void LiteralSubstitutionTree::remove(Literal* lit, Clause* cls)
{
  CALL("LiteralSubstitutionTree::remove");

  Renaming normalizer;
  Renaming::normalizeVariables(lit,normalizer);
  Literal* normLit=normalizer.apply(lit);

  BindingQueue bq;
  getBindings(normLit, bq);
  SubstitutionTree::remove(_nodes+getRootNodeIndex(lit), bq, LeafData(cls, lit));
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
  return getResultIterator<GeneralizationsIterator>(lit,
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

template<class Iterator>
SLQueryResultIterator LiteralSubstitutionTree::getResultIterator(Literal* lit,
	  bool complementary, bool retrieveSubstitutions)
{
  CALL("LiteralSubstitutionTree::getResultIterator");

  Node* root=_nodes[getRootNodeIndex(lit, complementary)];
  VirtualIterator<QueryResult> qrit=VirtualIterator<QueryResult>(
	    new Iterator(root, lit, retrieveSubstitutions) );
  return getMappingIterator(qrit, SLQueryResultFunctor());
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
