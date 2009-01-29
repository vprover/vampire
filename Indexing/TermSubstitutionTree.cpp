/**
 * @file TermSubstitutionTree.cpp
 * Implements class TermSubstitutionTree.
 */

#include "../Lib/Environment.hpp"
#include "../Lib/Metaiterators.hpp"
#include "../Kernel/Signature.hpp"
#include "../Kernel/Term.hpp"

#include "TermSubstitutionTree.hpp"

namespace Indexing
{

TermSubstitutionTree::TermSubstitutionTree()
: SubstitutionTree(env.signature->functions())
{
}

void TermSubstitutionTree::insert(TermList t, Literal* lit, Clause* cls)
{
  CALL("TermSubstitutionTree::insert");
  handleTerm(t,lit,cls, true);
}

void TermSubstitutionTree::remove(TermList t, Literal* lit, Clause* cls)
{
  CALL("TermSubstitutionTree::remove");
  handleTerm(t,lit,cls, false);
}

void TermSubstitutionTree::handleTerm(TermList t, Literal* lit, Clause* cls, bool insert)
{
  CALL("TermSubstitutionTree::handleTerm");

  LeafData ld(cls, lit, t);
  if(t.isOrdinaryVar()) {
    NOT_IMPLEMENTED;
    if(insert) {
      _vars.insert(ld);
    } else {
      _vars.remove(ld);
    }
  } else {
    ASS(t.isTerm());
    Term* term=t.term();

    Renaming normalizer;
    Renaming::normalizeVariables(term,normalizer);
    Term* normTerm=normalizer.apply(term);

    BindingQueue bq;
    getBindings(normTerm, bq);

    if(insert) {
      SubstitutionTree::insert(_nodes+getRootNodeIndex(normTerm), bq, ld);
    } else {
      SubstitutionTree::remove(_nodes+getRootNodeIndex(normTerm), bq, ld);
    }
  }
}


TermQueryResultIterator TermSubstitutionTree::getUnifications(TermList t,
	  bool retrieveSubstitutions)
{
  CALL("TermSubstitutionTree::getUnifications");
  if(t.isOrdinaryVar()) {
    NOT_IMPLEMENTED;
  } else {
    ASS(t.isTerm());
    return getResultIterator<UnificationsIterator>(t.term(), retrieveSubstitutions);
  }
}

TermQueryResultIterator TermSubstitutionTree::getGeneralizations(TermList t,
	  bool retrieveSubstitutions)
{
  CALL("TermSubstitutionTree::getGeneralizations");
  if(t.isOrdinaryVar()) {
    NOT_IMPLEMENTED;
  } else {
    ASS(t.isTerm());
    return getResultIterator<GeneralizationsIterator>(t.term(), retrieveSubstitutions);
  }
}

TermQueryResultIterator TermSubstitutionTree::getInstances(TermList t,
	  bool retrieveSubstitutions)
{
  CALL("TermSubstitutionTree::getInstances");
  if(t.isOrdinaryVar()) {
    NOT_IMPLEMENTED;
  } else {
    ASS(t.isTerm());
    return getResultIterator<InstancesIterator>(t.term(), retrieveSubstitutions);
  }
}


struct TermSubstitutionTree::TermQueryResultFunctor
{
  DECL_RETURN_TYPE(TermQueryResult);
  OWN_RETURN_TYPE operator() (const QueryResult& qr) {
    return TermQueryResult(qr.first->term, qr.first->literal,
	    qr.first->clause, qr.second);
  }
};

template<class Iterator>
TermQueryResultIterator TermSubstitutionTree::getResultIterator(Term* trm,
	  bool retrieveSubstitutions)
{
  CALL("TermSubstitutionTree::getResultIterator");
  Node* root=_nodes[getRootNodeIndex(trm)];
  VirtualIterator<QueryResult> qrit=VirtualIterator<QueryResult>(
	    new Iterator(root, trm, retrieveSubstitutions) );
  return pvi( getMappingIterator(qrit, TermQueryResultFunctor()) );
}

}
