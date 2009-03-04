/**
 * @file TermSubstitutionTree.cpp
 * Implements class TermSubstitutionTree.
 */

#include "../Lib/Environment.hpp"
#include "../Lib/Metaiterators.hpp"
#include "../Lib/SmartPtr.hpp"
#include "../Lib/Random.hpp"

#include "../Kernel/Signature.hpp"
#include "../Kernel/Term.hpp"
#include "../Kernel/Curryfier.hpp"

#include "TermSubstitutionTree.hpp"

namespace Indexing
{

using namespace Lib;
using namespace Kernel;

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

/**
 * According to value of @b insert, insert or remove term.
 */
void TermSubstitutionTree::handleTerm(TermList t, Literal* lit, Clause* cls, bool insert)
{
  CALL("TermSubstitutionTree::handleTerm");

  LeafData ld(cls, lit, t);
  if(t.isOrdinaryVar()) {
    if(insert) {
      _vars.insert(ld);
    } else {
      _vars.remove(ld);
    }
  } else {
    ASS(t.isTerm());
    Term* term=t.term();

    Renaming normalizer;
    normalizer.normalizeVariables(term);
    Term* normTerm=normalizer.apply(term);

    BindingQueue bq;
    getBindings(normTerm, bq);

    unsigned rootNodeIndex=getRootNodeIndex(normTerm);

    if(insert) {
      SubstitutionTree::insert(_nodes+rootNodeIndex, bq, ld);
    } else {
      SubstitutionTree::remove(_nodes+rootNodeIndex, bq, ld);
    }
  }
}


TermQueryResultIterator TermSubstitutionTree::getUnifications(TermList t,
	  bool retrieveSubstitutions)
{
  CALL("TermSubstitutionTree::getUnifications");
  if(t.isOrdinaryVar()) {
    return getAllUnifyingIterator(t,retrieveSubstitutions);
  } else {
    ASS(t.isTerm());
    return getResultIterator<UnificationsIterator>(t.term(), retrieveSubstitutions);
    if(_vars.isEmpty()) {
      return getResultIterator<UnificationsIterator>(t.term(), retrieveSubstitutions);
    } else {
      return pvi( getConcatenatedIterator(
	  ldIteratorToTQRIterator(LDSkipList::RefIterator(_vars), t, retrieveSubstitutions),
	  getResultIterator<UnificationsIterator>(t.term(), retrieveSubstitutions)) );
    }
  }
}


bool TermSubstitutionTree::generalizationExists(TermList t)
{
  if(!_vars.isEmpty()) {
    return true;
  }
  if(!t.isTerm()) {
    return false;
  }
  Term* trm=t.term();
  unsigned rootIndex=getRootNodeIndex(trm);
  Node* root=_nodes[rootIndex];
  if(!root) {
    return false;
  }
  if(root->isLeaf()) {
    return true;
  }
  return FastGeneralizationsIterator(this, root, trm, false).hasNext();
}

/**
 * Return iterator, that yields generalizations of the given term.
 */
TermQueryResultIterator TermSubstitutionTree::getGeneralizations(TermList t,
	  bool retrieveSubstitutions)
{
  CALL("TermSubstitutionTree::getGeneralizations");
  if(t.isOrdinaryVar()) {
    //only variables generalize other variables
    return ldIteratorToTQRIterator(LDSkipList::RefIterator(_vars), t, retrieveSubstitutions);
  } else {
    ASS(t.isTerm());
    if(_vars.isEmpty()) {
      return getResultIterator<FastGeneralizationsIterator>(t.term(), retrieveSubstitutions);
    } else {
      return pvi( getConcatenatedIterator(
	      ldIteratorToTQRIterator(LDSkipList::RefIterator(_vars), t, retrieveSubstitutions),
	      getResultIterator<FastGeneralizationsIterator>(t.term(), retrieveSubstitutions)) );
    }
  }
}

TermQueryResultIterator TermSubstitutionTree::getInstances(TermList t,
	  bool retrieveSubstitutions)
{
  CALL("TermSubstitutionTree::getInstances");
  if(t.isOrdinaryVar()) {
    return getAllUnifyingIterator(t,retrieveSubstitutions);
  } else {
    ASS(t.isTerm());
    return getResultIterator<InstancesIterator>(t.term(), retrieveSubstitutions);
  }
}

/**
 * Functor, that transforms &b QueryResult struct into
 * @b TermQueryResult.
 */
struct TermSubstitutionTree::TermQueryResultFn
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
  if(!root) {
    return TermQueryResultIterator::getEmpty();
  }
  if(root->isLeaf()) {
    LDIterator ldit=static_cast<Leaf*>(root)->allChildren();
    return ldIteratorToTQRIterator(ldit,TermList(trm),retrieveSubstitutions);
  }
  VirtualIterator<QueryResult> qrit=vi( new Iterator(this, root, trm, retrieveSubstitutions) );
  return pvi( getMappingIterator(qrit, TermQueryResultFn()) );
}

struct TermSubstitutionTree::LDToTermQueryResultFn
{
  DECL_RETURN_TYPE(TermQueryResult);
  OWN_RETURN_TYPE operator() (const LeafData& ld) {
    return TermQueryResult(ld.term, ld.literal, ld.clause);
  }
};

#define QRS_QUERY_BANK 0
#define QRS_RESULT_BANK 1

struct TermSubstitutionTree::LDToTermQueryResultWithSubstFn
{
  LDToTermQueryResultWithSubstFn()
  {
    _subst=RobSubstitutionSP(new RobSubstitution());
  }
  DECL_RETURN_TYPE(TermQueryResult);
  OWN_RETURN_TYPE operator() (const LeafData& ld) {
    return TermQueryResult(ld.term, ld.literal, ld.clause,
	    ResultSubstitution::fromSubstitution(_subst.ptr(),
		    QRS_QUERY_BANK,QRS_RESULT_BANK));
  }
private:
  RobSubstitutionSP _subst;
};

struct TermSubstitutionTree::LeafToLDIteratorFn
{
  DECL_RETURN_TYPE(LDIterator);
  OWN_RETURN_TYPE operator() (Leaf* l) {
    return l->allChildren();
  }
};

struct TermSubstitutionTree::UnifyingContext
{
  UnifyingContext(TermList queryTerm)
  : _queryTerm(queryTerm) {}
  bool enter(TermQueryResult qr)
  {
    ASS(qr.substitution);
    RobSubstitution* subst=qr.substitution->tryGetRobSubstitution();
    ASS(subst);
    ALWAYS(subst->unify(_queryTerm, QRS_QUERY_BANK, qr.term, QRS_RESULT_BANK));
    return true;
  }
  void leave(TermQueryResult qr)
  {
    RobSubstitution* subst=qr.substitution->tryGetRobSubstitution();
    ASS(subst);
    subst->reset();
  }
private:
  TermList _queryTerm;
};

template<class LDIt>
TermQueryResultIterator TermSubstitutionTree::ldIteratorToTQRIterator(LDIt ldIt,
	TermList queryTerm, bool retrieveSubstitutions)
{
  if(retrieveSubstitutions) {
    return pvi( getContextualIterator(
	    getMappingIterator(
		    ldIt,
		    LDToTermQueryResultWithSubstFn()),
	    UnifyingContext(queryTerm)) );
  } else {
    return pvi( getMappingIterator(
	    ldIt,
	    LDToTermQueryResultFn()) );
  }
}

TermQueryResultIterator TermSubstitutionTree::getAllUnifyingIterator(TermList var,
	  bool retrieveSubstitutions)
{
  return ldIteratorToTQRIterator(
	    getConcatenatedIterator(
		    getFlattenedIterator(
			    getMappingIterator(
				    vi( new LeafIterator(this) ),
				    LeafToLDIteratorFn())),
		    LDSkipList::RefIterator(_vars)),
	    var, retrieveSubstitutions);
}


}
