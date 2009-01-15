/**
 * @file TermSubstitutionTree.cpp
 * Implements class TermSubstitutionTree.
 */

#include "../Lib/Environment.hpp"
#include "../Lib/Metaiterators.hpp"
#include "../Kernel/Signature.hpp"
#include "../Kernel/Term.hpp"

#include "TermSubstitutionTree.hpp"

using namespace Indexing;

TermSubstitutionTree::TermSubstitutionTree()
: SubstitutionTree(env.signature->functions())
{
}

void TermSubstitutionTree::insert(TermList t, Literal* lit, Clause* cls)
{
  CALL("TermSubstitutionTree::insert");

  LeafData ld(cls, lit, t);
  if(t.isOrdinaryVar()) {
    NOT_IMPLEMENTED;
    _vars.insert(ld);
  } else {
    ASS(t.isTerm());
    Term* term=t.term();

    BindingQueue bq;
    getBindings(term, bq);

    SubstitutionTree::insert(_nodes+getRootNodeIndex(term), bq, ld);
  }
}

void TermSubstitutionTree::remove(TermList t, Literal* lit, Clause* cls)
{
  CALL("TermSubstitutionTree::remove");

  LeafData ld(cls, lit, t);
  if(t.isOrdinaryVar()) {
    NOT_IMPLEMENTED;
    _vars.remove(ld);
  } else {
    ASS(t.isTerm());
    Term* term=t.term();

    BindingQueue bq;
    getBindings(term, bq);

    SubstitutionTree::remove(_nodes+getRootNodeIndex(term), bq, ld);
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


class TermSubstitutionTree::TermQueryResultFunctor
{
public:
  TermQueryResult operator() (QueryResult qr) {
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
  return getMappingIterator<TermQueryResult>(qrit, TermQueryResultFunctor());
}

