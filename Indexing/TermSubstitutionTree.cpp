
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

TermSubstitutionTree::TermSubstitutionTree(bool useC, bool usePlcHlds)
: SubstitutionTree(env.signature->functions(),useC), _usePlcHlds(usePlcHlds)
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

    if(_usePlcHlds){
      term = toPlaceHolders(term);
      
      if(isPlaceHolder(term)){
        unsigned sort = SortHelper::getResultSort(term);
        LDSkipList* lds;        
        if(insert){
          if(_placeHolders.find(sort, lds)){
            lds->insert(ld);          
          } else {
            LDSkipList* lds = new LDSkipList();
            lds->insert(ld);
            _placeHolders.insert(sort, lds);          
          }
        } else {
          if(_placeHolders.find(sort, lds)){
            lds->remove(ld);          
          }
        }
        return;
      }
    }
    
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

    Term* term;

    if(_usePlcHlds){
      term = toPlaceHolders(t.term());
    } else {
      term = t.term();
    }

    // false here means without constraints
    auto it1 = getResultIterator<UnificationsIterator>(term, retrieveSubstitutions,false);
    if(_vars.isEmpty()) { 
      if(!_usePlcHlds){
        return it1;
      } else {
        unsigned sort = SortHelper::getResultSort(t.term());
        if(_placeHolders.find(sort)){
          LDSkipList* lds = _placeHolders.get(sort);
          auto it2 = ldIteratorToTQRIterator(LDSkipList::RefIterator(*lds), t, false,false);
          return pvi( getConcatenatedIterator(it1, it2));        
        } else {
          return it1;
        }
      }
    } else {
      auto it2 = ldIteratorToTQRIterator(LDSkipList::RefIterator(_vars), t, retrieveSubstitutions,false);
      auto it3 = getConcatenatedIterator(it1, it2);
      if(!_usePlcHlds){
        return pvi( it3 );
      } else {
        unsigned sort = SortHelper::getResultSort(t.term());
        if(_placeHolders.find(sort)){
          LDSkipList* lds = _placeHolders.get(sort);
          auto it4 = ldIteratorToTQRIterator(LDSkipList::RefIterator(*lds), t, false,false);
          return pvi( getConcatenatedIterator(it3, it4));        
        } else {
          return pvi( it3 );  
        }
      }
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
  DECL_RETURN_TYPE(TermQueryResult);
  OWN_RETURN_TYPE operator() (const QueryResult& qr) {
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
  DECL_RETURN_TYPE(TermQueryResult);
  OWN_RETURN_TYPE operator() (const LeafData& ld) {
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
  DECL_RETURN_TYPE(TermQueryResult);
  OWN_RETURN_TYPE operator() (const LeafData& ld) {
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
  DECL_RETURN_TYPE(LDIterator);
  OWN_RETURN_TYPE operator() (Leaf* l) {
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

/** Takes higher-order term in applicative form and replaces
  * all subterms of the form @(@(...(X, t1) ... tn) or @(@(...(COMB, t1) ... tn)
  * with a special term called a placeHolder term (represented by #).
  */

Term* TermSubstitutionTree::toPlaceHolders(Term* term){
  CALL("TermSubstitutionTree::toPlaceHolders");

  static Stack<TermList*> toDo(8);
  static Stack<Term*> terms(8);
  static Stack<bool> modified(8);
  static Stack<TermList> args(8);
  ASS(toDo.isEmpty());
  ASS(terms.isEmpty());
  modified.reset();
  args.reset();

  if(hasVariableOrCombinatorHead(TermList(term))){
   return Term::placeHolderTerm(SortHelper::getResultSort(term)); 
  }
  
  modified.push(false);
  toDo.push(term->args());

  for (;;) {
    TermList* tt=toDo.pop();
    if (tt->isEmpty()) {
      if (terms.isEmpty()) {
        //we're done, args stack contains modified arguments
        //of the literal.
        ASS(toDo.isEmpty());
        break;
      }
      Term* orig=terms.pop();
      if (!modified.pop()) {
        args.truncate(args.length() - orig->arity());
        args.push(TermList(orig));
        continue;
      }
      //here we assume, that stack is an array with
      //second topmost element as &top()-1, third at
      //&top()-2, etc...
      TermList* argLst=&args.top() - (orig->arity()-1);
      args.truncate(args.length() - orig->arity());

      args.push(TermList(Term::create(orig,argLst)));
      modified.setTop(true);
      continue;
    }
    toDo.push(tt->next());

    TermList tl=*tt;
    if (tl.isVar()) {
      args.push(tl);
      continue;
    }
    ASS(tl.isTerm());
    if(hasVariableOrCombinatorHead(tl)) {
      args.push(TermList(Term::placeHolderTerm(SortHelper::getResultSort(tl.term())))); 
      modified.setTop(true);
      continue;
    }
    Term* t=tl.term();
    terms.push(t);
    modified.push(false);
    toDo.push(t->args());
  }
  ASS(toDo.isEmpty());
  ASS(terms.isEmpty());
  ASS_EQ(modified.length(),1);
  ASS_EQ(args.length(),term->arity());

  if (!modified.pop()) {
    return term;
  }
  
  TermList* argLst=&args.top() - (term->arity()-1);
  return Term::create(term,argLst);

}

/**
  * Returns true if the head symbol of applicative term ts
  * is either a variable or a combinator. 
  * @author Ahmed Bhayat
  * @location Manchester
  */
bool TermSubstitutionTree::hasVariableOrCombinatorHead(TermList ts)
{
  CALL("TermSubstitutionTree::hasVariableOrCombinatorHead");
  
  //cout << "The termspec is " + ts.toString() << endl;

  auto isCombSym = [] (Signature::Symbol* sym1) { 
       return
      (sym1->getConst() == Signature::Symbol::S_COMB ||
       sym1->getConst() == Signature::Symbol::B_COMB ||
       sym1->getConst() == Signature::Symbol::C_COMB ||
       sym1->getConst() == Signature::Symbol::I_COMB ||
       sym1->getConst() == Signature::Symbol::K_COMB);
  };

  if(ts.isVar()){
    return false;
  } else {
    ASS(ts.isTerm());
    Signature::Symbol* sym = env.signature->getFunction(ts.term()->functor());
    if(isCombSym(sym)){
      return true;
    }
    while(sym->hOLAPP()){
      ts = *(ts.term()->nthArgument(0));
      if(ts.isVar()){
        return true;
      }
      sym = env.signature->getFunction(ts.term()->functor());
      if(isCombSym(sym)){
        return true;
      }
    }
    return false;
  }

}

}

