
/*
 * File TermSubstitutionTree.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file TermSubstitutionTree.cpp
 * Implements class TermSubstitutionTree.
 */

#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Random.hpp"
#include "Lib/SmartPtr.hpp"
#include "Lib/TimeCounter.hpp"

#include "Kernel/Matcher.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"

#include "Shell/Options.hpp"

#include "TermSubstitutionTree.hpp"

namespace Indexing
{

using namespace Lib;
using namespace Kernel;

TermSubstitutionTree::TermSubstitutionTree(bool useC)
: SubstitutionTree(env.signature->functions(),useC)
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
      // why is this case needed?
      _vars.remove(ld);
    }
  } else {
    ASS(t.isTerm());
    Term* term=t.term();

    Term* normTerm=Renaming::normalize(term);

    BindingMap svBindings;
    getBindings(normTerm, svBindings);

    unsigned rootNodeIndex=getRootNodeIndex(normTerm);

    if(insert) {
      SubstitutionTree::insert(&_nodes[rootNodeIndex], svBindings, ld);
    } else {
      SubstitutionTree::remove(&_nodes[rootNodeIndex], svBindings, ld);
    }
  }
}


TermQueryResultIterator TermSubstitutionTree::getUnifications(TermList t,
	  bool retrieveSubstitutions)
{
  CALL("TermSubstitutionTree::getUnifications");
  if(t.isOrdinaryVar()) {
    return getAllUnifyingIterator(t,retrieveSubstitutions,false);
  } else {
    ASS(t.isTerm());
    if(_vars.isEmpty()) {
      // false here means without constraints
      return getResultIterator<UnificationsIterator>(t.term(), retrieveSubstitutions,false);
    } else {
      return pvi( getConcatenatedIterator(
          // false here means without constraints
	  ldIteratorToTQRIterator(LDSkipList::RefIterator(_vars), t, retrieveSubstitutions,false),
          // false here means without constraints
	  getResultIterator<UnificationsIterator>(t.term(), retrieveSubstitutions,false)) );
    }
  }
}

//TODO code sharing with getUnifications
TermQueryResultIterator TermSubstitutionTree::getUnificationsWithConstraints(TermList t,
          bool retrieveSubstitutions)
{
  CALL("TermSubstitutionTree::getUnificationsWithConstraints");

  //cout << "getUnificationsWithConstraints of " << t.toString() << endl;

  // don't need to do anything different in the case of t being a variable
  if(t.isOrdinaryVar()) {
    return getAllUnifyingIterator(t,retrieveSubstitutions,false);
  } else {
    ASS(t.isTerm());
    if(_vars.isEmpty()) {
      // true here means with constraints
      return getResultIterator<UnificationsIterator>(t.term(), retrieveSubstitutions,true);
    } else {
      return pvi( getConcatenatedIterator(
          //we use false here as we are giving variables so no constraints will be needed
          ldIteratorToTQRIterator(LDSkipList::RefIterator(_vars), t, retrieveSubstitutions,false),
          //true here means with constraints
          getResultIterator<UnificationsIterator>(t.term(), retrieveSubstitutions,true)) );
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
  // Currently we do not need to generate constraints with generalisations
  // FastGeneralizationsIterator does not support constraints anyway
  bool useC = false; 
  return FastGeneralizationsIterator(this, root, trm, false,false,false,useC).hasNext();
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
    return ldIteratorToTQRIterator(LDSkipList::RefIterator(_vars), t, retrieveSubstitutions,false);
  } else {
    ASS(t.isTerm());
    if(_vars.isEmpty()) {
      return getResultIterator<FastGeneralizationsIterator>(t.term(), retrieveSubstitutions,false);
    } else {
      return pvi( getConcatenatedIterator(
	      ldIteratorToTQRIterator(LDSkipList::RefIterator(_vars), t, retrieveSubstitutions,false),
	      getResultIterator<FastGeneralizationsIterator>(t.term(), retrieveSubstitutions,false)) );
    }
  }
}

TermQueryResultIterator TermSubstitutionTree::getInstances(TermList t,
	  bool retrieveSubstitutions)
{
  CALL("TermSubstitutionTree::getInstances");
  if(t.isOrdinaryVar()) {
    return getAllUnifyingIterator(t,retrieveSubstitutions,false);
  } else {
    ASS(t.isTerm());
    return getResultIterator<FastInstancesIterator>(t.term(), retrieveSubstitutions,false);
  }
}

/**
 * Functor, that transforms &b QueryResult struct into
 * @b TermQueryResult.
 */
struct TermSubstitutionTree::TermQueryResultFn
{
  TermQueryResult operator() (const QueryResult& qr) {
    return TermQueryResult(qr.first.first->term, qr.first.first->literal,
	    qr.first.first->clause, qr.first.second,qr.second);
  }
};

template<class Iterator>
TermQueryResultIterator TermSubstitutionTree::getResultIterator(Term* trm,
	  bool retrieveSubstitutions,bool withConstraints)
{
  CALL("TermSubstitutionTree::getResultIterator");

  //cout << "getResultIterator " << trm->toString() << endl;

  TermQueryResultIterator result = TermQueryResultIterator::getEmpty();
  
  Node* root = _nodes[getRootNodeIndex(trm)];

  if(root){
    if(root->isLeaf()) {
      LDIterator ldit=static_cast<Leaf*>(root)->allChildren();
      result = ldIteratorToTQRIterator(ldit,TermList(trm),retrieveSubstitutions,false);
    }
    else{
      VirtualIterator<QueryResult> qrit=vi( new Iterator(this, root, trm, retrieveSubstitutions,false,false, withConstraints) );
      result = pvi( getMappingIterator(qrit, TermQueryResultFn()) );
    }
  }

  // DO NOT ALLOW UNIFICATIONS AT THE TOP LEVEL
  if(false){
    ASS(retrieveSubstitutions);
    // this true means that I am allowed to pass a non-variable term to getAllUnifyingIterator
    TermQueryResultIterator other = getAllUnifyingIterator(TermList(trm),retrieveSubstitutions,true); 
    result = pvi(getConcatenatedIterator(result,other));
  }
  return result;
}

struct TermSubstitutionTree::LDToTermQueryResultFn
{
  TermQueryResult operator() (const LeafData& ld) {
    return TermQueryResult(ld.term, ld.literal, ld.clause);
  }
};

#define QRS_QUERY_BANK 0
#define QRS_RESULT_BANK 1

struct TermSubstitutionTree::LDToTermQueryResultWithSubstFn
{
  LDToTermQueryResultWithSubstFn(bool wc) : _withConstraints(wc)
  {
    _subst=RobSubstitutionSP(new RobSubstitution());
    _constraints=UnificationConstraintStackSP(new Stack<UnificationConstraint>());
  }
  TermQueryResult operator() (const LeafData& ld) {
    if(_withConstraints){
      return TermQueryResult(ld.term, ld.literal, ld.clause,
            ResultSubstitution::fromSubstitution(_subst.ptr(),
                    QRS_QUERY_BANK,QRS_RESULT_BANK),
            _constraints);
    }
    else{
      return TermQueryResult(ld.term, ld.literal, ld.clause,
	    ResultSubstitution::fromSubstitution(_subst.ptr(),
		    QRS_QUERY_BANK,QRS_RESULT_BANK));
    }
  }
private:
  bool _withConstraints;
  RobSubstitutionSP _subst;
  UnificationConstraintStackSP _constraints;
};

struct TermSubstitutionTree::LeafToLDIteratorFn
{
  LDIterator operator() (Leaf* l) {
    CALL("TermSubstitutionTree::LeafToLDIteratorFn()");
    return l->allChildren();
  }
};

struct TermSubstitutionTree::UnifyingContext
{
  UnifyingContext(TermList queryTerm,bool withConstraints)
  : _queryTerm(queryTerm),_withConstraints(withConstraints) {}
  bool enter(TermQueryResult qr)
  {
    //if(_withConstraints){ cout << "enter " << qr.term << endl; }

    ASS(qr.substitution);
    RobSubstitution* subst=qr.substitution->tryGetRobSubstitution();
    ASS(subst);
    bool unified = subst->unify(_queryTerm, QRS_QUERY_BANK, qr.term, QRS_RESULT_BANK);
    //unsigned srt;
/*
    if(_withConstraints && !unified && 
       SortHelper::tryGetResultSort(_queryTerm,srt) && srt < Sorts::FIRST_USER_SORT && srt!=Sorts::SRT_DEFAULT){
      UnificationConstraintStackSP constraints = qr.constraints;
      ASS(!constraints.isEmpty());
      //current usage tells us that if we are querying withConstraints then
      //we assume the unification will fail

      static Options::UnificationWithAbstraction opt = env.options->unificationWithAbstraction();
      bool queryInterp = (theory->isInterpretedFunction(_queryTerm) || theory->isInterpretedConstant(_queryTerm));
      bool termInterp = (theory->isInterpretedFunction(qr.term) || theory->isInterpretedConstant(qr.term));
      bool bothNumbers = (theory->isInterpretedConstant(_queryTerm) && theory->isInterpretedConstant(qr.term));

      // I don't expect okay to be false at this point as if one is a variable the above unify would succeed 
      bool okay = _queryTerm.isTerm() && qr.term.isTerm();
      ASS(okay);
      switch(opt){
        case Options::UnificationWithAbstraction::INTERP_ONLY:
          okay &= (queryInterp && termInterp && !bothNumbers);
          break;
        case Options::UnificationWithAbstraction::ONE_INTERP:
          okay &= !bothNumbers && (queryInterp || termInterp);
          break;
        case Options::UnificationWithAbstraction::CONSTANT:
          okay &= !bothNumbers && (queryInterp || termInterp);
          okay &= (queryInterp || env.signature->functionArity(_queryTerm.term()->functor()));
          okay &= (termInterp || env.signature->functionArity(qr.term.term()->functor()));
          break;
      }
      if(okay){
        // cout << "UNIFY " <<  _queryTerm.toString()+", "+qr.term.toString() << endl;
        unsigned x = 0;
        TermList trmVar = TermList(x,true); 
        subst->bindSpecialVar(x,qr.term,QRS_RESULT_BANK);
        pair<TermList,TermList> constraint = make_pair(_queryTerm,trmVar);
        //cout << "push constraint" << endl;
        constraints->push(constraint);
        unified=true;
      }
    }
*/
    ASS(unified || _withConstraints);
    return unified;
  }
  void leave(TermQueryResult qr)
  {
    RobSubstitution* subst=qr.substitution->tryGetRobSubstitution();
    ASS(subst);
    subst->reset();
    if(!qr.constraints.isEmpty()){
      //cout << "reset constraints" << endl;
      qr.constraints->reset();
    }
  }
private:
  TermList _queryTerm;
  bool _withConstraints;
};

template<class LDIt>
TermQueryResultIterator TermSubstitutionTree::ldIteratorToTQRIterator(LDIt ldIt,
	TermList queryTerm, bool retrieveSubstitutions,bool withConstraints)
{
  CALL("TermSubstitutionTree::ldIteratorToTQRIterator");
  // only call withConstraints if we are also getting substitions, the other branch doesn't handle constraints
  ASS(retrieveSubstitutions | !withConstraints); 

  if(retrieveSubstitutions) {
    return pvi( getContextualIterator(
	    getMappingIterator(
		    ldIt,
		    LDToTermQueryResultWithSubstFn(withConstraints)),
	    UnifyingContext(queryTerm,withConstraints)) );
  } else {
    return pvi( getMappingIterator(
	    ldIt,
	    LDToTermQueryResultFn()) );
  }
}

TermQueryResultIterator TermSubstitutionTree::getAllUnifyingIterator(TermList trm,
	  bool retrieveSubstitutions,bool withConstraints)
{
  CALL("TermSubstitutionTree::getAllUnifyingIterator");

  //if(withConstraints){ cout << "getAllUnifyingIterator for " << trm.toString() << endl; }

  ASS(trm.isVar() || withConstraints);

  auto it1 = getFlattenedIterator(getMappingIterator(vi( new LeafIterator(this) ), LeafToLDIteratorFn()));

  // If we are searching withConstraints it means that we have already added in
  // the results related to _vars, we are only interested in non-unifying leaves

  // STOP DOING THIS AT THE TOP LEVEL
  if(false){
    return ldIteratorToTQRIterator(it1,trm, retrieveSubstitutions,withConstraints);
  }
  else{
    return ldIteratorToTQRIterator(
	    getConcatenatedIterator(it1,LDSkipList::RefIterator(_vars)),
	    trm, retrieveSubstitutions,withConstraints);
  }
}


}
