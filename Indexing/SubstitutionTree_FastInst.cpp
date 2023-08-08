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
 * @file SubstitutionTree_FastInst.cpp
 * Implements class SubstitutionTree::FastInst, its child classes
 * and some auxiliary classes.
 */

#include "Lib/Allocator.hpp"
#include "Lib/Recycled.hpp"

#include "Kernel/Matcher.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/TermIterators.hpp"

#include "SubstitutionTree.hpp"

namespace Indexing
{

std::ostream& operator<< (ostream& out, SubstitutionTree::InstMatcher::TermSpec ts )
{
  CALL("operator<<(ostream&,SubstitutionTree::InstMatcher::TermSpec)");

  out<<ts.toString();
  return out;
}


class SubstitutionTree::InstMatcher::Substitution
: public ResultSubstitution
{
public:
  CLASS_NAME(SubstitutionTree::InstMatcher::Substitution);
  USE_ALLOCATOR(SubstitutionTree::InstMatcher::Substitution);
  
  Substitution(InstMatcher* parent, Renaming* resultDenormalizer)
  : _parent(parent), _resultDenormalizer(resultDenormalizer)
  {}
  ~Substitution()
  {
  }

  TermList applyToBoundQuery(TermList t) override
  {
    CALL("SubstitutionTree::InstMatcher::Substitution::applyToBoundQuery");

    return SubstHelper::apply(t, *this);
  }

  TermList apply(unsigned var)
  {
    CALL("SubstitutionTree::InstMatcher::Substitution::apply");

    TermList normalized=_parent->derefQueryBinding(var);
    ASS_REP(!normalized.isTerm() || normalized.term()->shared(), normalized);
    return _resultDenormalizer->apply(normalized);
  }
  
  bool isIdentityOnResultWhenQueryBound() override
  { return true; }

  

  virtual void output(std::ostream& out) const final override 
  { out << "InstMatcher::Substitution(<output unimplemented>)"; }
private:
  InstMatcher* _parent;
  Renaming* _resultDenormalizer;
};


ResultSubstitutionSP SubstitutionTree::InstMatcher::getSubstitution(Renaming* resultDenormalizer)
{
  CALL("SubstitutionTree::InstMatcher::getSubstitution");

  return ResultSubstitutionSP(
	  new Substitution(this, resultDenormalizer));
}

TermList SubstitutionTree::InstMatcher::derefQueryBinding(unsigned var)
{
  CALL("SubstitutionTree::InstMatcher::derefQueryBinding");

  TermList tvar0(var, false);
  TermList tvar=tvar0;

  TermSpec varBinding;
  {
    TermList val;
    if(_derefBindings->find(tvar, val)) {
      return val;
    }
    //only bound values can be passed to this function
    ALWAYS(_bindings->find(tvar, varBinding));

    if(varBinding.isFinal()) {
      ALWAYS(_derefBindings->insert(tvar, varBinding.t));
      return varBinding.t;
    }
  }
  static Stack<DerefTask> toDo;
  toDo.reset();

  for(;;) {
    while(!varBinding.isFinal() && !varBinding.t.isTerm()) {
      ASS(varBinding.t.isVar());
      ASS(!varBinding.q || !varBinding.t.isOrdinaryVar());


      TermList bvar=varBinding.t;
      TermList derefBoundTerm;

      if(_derefBindings->find(bvar, derefBoundTerm)) {
        ALWAYS(_derefBindings->insert(tvar, derefBoundTerm));
      }

      ALWAYS(_bindings->find(bvar,varBinding));
    }
    if(varBinding.isFinal()) {
      ALWAYS(_derefBindings->insert(tvar, varBinding.t));
      goto next_loop;
    }
    {
      ASS(varBinding.t.isTerm());
      toDo.push(DerefTask(tvar, varBinding));
      VariableIterator vit(varBinding.t);
      while(vit.hasNext()) {
        TermList btv=vit.next(); //bound term variable
        if(varBinding.q || btv.isSpecialVar()) {
          ASS(_bindings->find(btv));
          if(!_derefBindings->find(btv)) {
            toDo.push(DerefTask(btv));
          }
        }
      }
    }
    next_loop:
    while(toDo.isNonEmpty() && toDo.top().buildDerefTerm()) {
      tvar=toDo.top().var;
      TermSpec tspec=toDo.pop().trm;
      DerefApplicator applicator(this, tspec.q);
      TermList derefTerm=SubstHelper::applySV(tspec.t, applicator);
      ASS_REP(!derefTerm.isTerm() || derefTerm.term()->shared(), derefTerm);
      ALWAYS(_derefBindings->insert(tvar, derefTerm));
    }
    if(toDo.isEmpty()) {
      break;
    }
    tvar=toDo.pop().var;
    ALWAYS(_bindings->find(tvar, varBinding));
  };
  return _derefBindings->get(tvar0);
}

SubstitutionTree::InstMatcher::TermSpec SubstitutionTree::InstMatcher::deref(TermList var)
{
  CALL("SubstitutionTree::InstMatcher::deref");
  ASS_REP(var.isVar(), var.tag());

#if VDEBUG
  int ctr=0;
#endif
  for(;;) {
    TermSpec res;
    if(!_bindings->find(var, res)) {
	return TermSpec(var.isOrdinaryVar() ? true : false, var);
    }
    if( res.t.isTerm() || (!res.q && res.t.isOrdinaryVar()) ) {
	return res;
    }
    ASS(!res.q || !res.t.isSpecialVar());
    var=res.t;
#if VDEBUG
    ctr++;
    ASS_L(ctr,1000000); //assert that there are no cycles
#endif
  }
}

/**
 * Undo one call to the @b matchNext method with separate param
 * set to @b true and all other @b matchNext calls that were joined to it.
 */
void SubstitutionTree::InstMatcher::backtrack()
{
  CALL("SubstitutionTree::InstMatcher::backtrack");

  for(;;) {
    TermList boundVar=_boundVars->pop();
    if(boundVar.isEmpty()) {
      break;
    }
    _bindings->remove(boundVar);
  }
}

/**
 * Try to undo one call to the @b matchNext method with separate param
 * set to @b true and all other @b matchNext calls that were joined to it.
 * Return true iff successful. (The failure can be due to the fact there
 * is no separated @b matchNext call to be undone. In this case every binding
 * on the @b _boundVars stack would be undone.)
 */
bool SubstitutionTree::InstMatcher::tryBacktrack()
{
  CALL("SubstitutionTree::InstMatcher::tryBacktrack");

  while(_boundVars->isNonEmpty()) {
    TermList boundVar=_boundVars->pop();
    if(boundVar.isEmpty()) {
      return true;
    }
    _bindings->remove(boundVar);
  }
  return false;
}


bool SubstitutionTree::InstMatcher::matchNext(unsigned specVar, TermList nodeTerm, bool separate)
{
  CALL("SubstitutionTree::InstMatcher::matchNext");

  if(separate) {
    TermList sep;
    sep.makeEmpty();
    _boundVars->push(sep);
  }

#if VDEBUG
  {
    //we assert that all the special variables in the nodeTerm are unbound
    VariableIterator vit(nodeTerm);
    while(vit.hasNext()) {
      TermList var=vit.next();
      if(var.isSpecialVar()) {
  ASS(!isBound(var));
      }
    }
  }
#endif
  return matchNextAux(TermList(specVar, true), nodeTerm, separate);
}

/**
 * Match @b nodeTerm to term in the special variable @b specVar.
 * If @b separate is true, join this match with the previous one
 * on backtracking stack, so they will be undone both by one
 * call to the backtrack() method.
 */
bool SubstitutionTree::InstMatcher::matchNextAux(TermList queryTerm, TermList nodeTerm, bool separate)
{
  CALL("SubstitutionTree::InstMatcher::matchNextAux");

  unsigned specVar;
  TermSpec tsBinding;

  TermSpec tsNode(false, nodeTerm);

  if(queryTerm.isSpecialVar()){
    specVar = queryTerm.var();
    if(!findSpecVarBinding(specVar,tsBinding)) {
      bind(TermList(specVar,true), tsNode);
      return true;
    }
  } else {
    tsBinding = TermSpec(true, queryTerm);
  }

  if(tsBinding.q && tsBinding.t.isOrdinaryVar() && !isBound(tsBinding.t)) {
    bind(tsBinding.t, tsNode);
    return true;
  }

  bool success;

  if(nodeTerm.isTerm() && nodeTerm.term()->shared() && nodeTerm.term()->ground() &&
      tsBinding.q && tsBinding.t.isTerm() && tsBinding.t.term()->ground()) {
    success=nodeTerm.term()==tsBinding.t.term();
    goto finish;
  }

  static Stack<pair<TermSpec,TermSpec> > toDo;
  static DisagreementSetIterator dsit;

  toDo.reset();
  toDo.push(make_pair(tsBinding, tsNode));

  while(toDo.isNonEmpty()) {
    TermSpec ts1=toDo.top().first;
    TermSpec ts2=toDo.pop().second;
//    ASS(!ts2.q); //ts2 is always a node term

    dsit.reset(ts1.t, ts2.t, ts1.q!=ts2.q);
    while(dsit.hasNext()) {
      pair<TermList,TermList> disarg=dsit.next();
      TermList dt1=disarg.first;
      TermList dt2=disarg.second;

      bool dt1Bindable= !dt1.isTerm() && (ts1.q || !dt1.isOrdinaryVar());
      bool dt2Bindable= !dt2.isTerm() && (ts2.q || !dt2.isOrdinaryVar());

      if(!dt1Bindable && !dt2Bindable) {
        success=false;
        goto finish;
      }

      //we try to bind ordinary variables first, as binding a special
      //variable to an ordinary variable does not allow us to cut off
      //children when entering a node (a term to bind the special variable
      //may come later, so we want to keep it unbound)

      if(ts1.q && dt1.isOrdinaryVar() && !isBound(dt1)) {
        bind(dt1, TermSpec(ts2.q,dt2));
        continue;
      }
      if(ts2.q && dt2.isOrdinaryVar() && !isBound(dt2)) {
        bind(dt2, TermSpec(ts1.q,dt1));
        continue;
      }

      if(dt2.isSpecialVar() && !isBound(dt2)) {
        ASS(!ts2.q);
        bind(dt2, TermSpec(ts1.q,dt1));
        continue;
      }
      if(dt1.isSpecialVar() && !isBound(dt1)) {
        ASS(!ts1.q);
        bind(dt1, TermSpec(ts2.q,dt2));
        continue;
      }

      TermSpec deref1=TermSpec(ts1.q, dt1);
      TermSpec deref2=TermSpec(ts2.q, dt2);
      if(dt1Bindable) {
        ASS(isBound(dt1)); //if unbound, we would have assigned it earlier
        deref1=deref(dt1);
      }
      if(dt2Bindable) {
        ASS(isBound(dt2));
        deref2=deref(dt2);
      }

      toDo.push(make_pair(deref1, deref2));
    }
  }
  success=true;

finish:
  if(!success) {
    //if this matching was joined to the previous one, we don't
    //have to care about unbinding as caller will do this by calling
    //backtrack for the matching we're joined to.
    if(separate) {
      //we have to unbind variables, that were bound.
      backtrack();
    }
  }
  return success;
}

bool SubstitutionTree::FastInstancesIterator::hasNext()
{
  CALL("SubstitutionTree::FastInstancesIterator::hasNext");

  while(!_ldIterator.hasNext() && findNextLeaf()) {}
  return _ldIterator.hasNext();
}

#undef LOGGING
#define LOGGING 0

SubstitutionTree::QueryResultIter SubstitutionTree::FastInstancesIterator::next()
{
  CALL("SubstitutionTree::FastInstancesIterator::next");

  while(!_ldIterator.hasNext() && findNextLeaf()) {}
  ASS(_ldIterator.hasNext());
  auto ld = _ldIterator.next();

  if(_retrieveSubstitution) {
    _resultDenormalizer.reset();
    bool ground=_literalRetrieval
        ? ld->literal->ground()
        : (ld->term.isTerm() && ld->term.term()->ground());
    if(!ground) {
      Renaming normalizer(0, NORM_RESULT_BANK);
      if(_literalRetrieval) {
        normalizer.normalizeVariables(ld->literal);
      } else {
        normalizer.normalizeVariables(ld->term);
      }
      _resultDenormalizer.makeInverse(normalizer);
    }
    // TODO update this once we make matching iterators templated on matching algorithm
    // or remove altogether if we go with Joe's refactor
    return pvi(getSingletonIterator(QueryResult(ld, _subst.getSubstitution(&_resultDenormalizer))));
  } else {
    return pvi(getSingletonIterator(QueryResult(ld, ResultSubstitutionSP())));
  }
}
#undef LOGGING
#define LOGGING 0

/**
 * Find next leaf that contains instances of the query
 * term. If there is no such, return false.
 */
bool SubstitutionTree::FastInstancesIterator::findNextLeaf()
{
  CALL("SubstitutionTree::FastInstancesIterator::findNextLeaf");

  Node* curr;
  bool sibilingsRemain = false;
  if(_inLeaf) {
    if(_alternatives->isEmpty()) {
      return false;
    }
    _subst.backtrack();
    _inLeaf=false;
    curr=0;
  } else {
    if(!_root) {
      //If we aren't in a leaf and the findNextLeaf method has already been called,
      //it means that we're out of leafs.
      return false;
    }
    curr=_root;
    _root=0;
    sibilingsRemain=enterNode(curr);
  }
  for(;;) {
main_loop_start:
    unsigned currSpecVar = 0;

    if(curr) {
      if(sibilingsRemain) {
        ASS(_nodeTypes->top()!=UNSORTED_LIST || *static_cast<Node**>(_alternatives->top()));
        currSpecVar = _specVarNumbers->top();
      } else {
	      currSpecVar = _specVarNumbers->pop();
      }
    }
    //let's find a node we haven't been to...
    while(curr==0 && _alternatives->isNonEmpty()) {
      void* currAlt=_alternatives->pop();
      if(!currAlt) {
        //there's no alternative at this level, we have to backtrack
        _nodeTypes->pop();
        _specVarNumbers->pop();
        if(_alternatives->isNonEmpty()) {
          _subst.backtrack();
        }
        continue;
      }

      NodeAlgorithm parentType = _nodeTypes->top();

      //the fact that we have alternatives means that here we are
      //matching by a variable (as there is always at most one child
      //for matching by term)
      if(parentType==UNSORTED_LIST) {
        Node** alts=static_cast<Node**>(currAlt);
        curr=*(alts++);
        if(*alts) {
          _alternatives->push(alts);
          sibilingsRemain=true;
        } else {
          sibilingsRemain=false;
        }
      } else {
        ASS_EQ(parentType,SKIP_LIST)
        auto alts = static_cast<SListIntermediateNode::NodeSkipList::Node *>(currAlt);
        ASS(alts);

        curr=alts->head();
        if(alts->tail()) {
          _alternatives->push(alts->tail());
          sibilingsRemain=true;
        } else {
          sibilingsRemain=false;
        }
      }

      if(sibilingsRemain) {
        currSpecVar = _specVarNumbers->top();
      } else {
        _nodeTypes->pop();
        currSpecVar = _specVarNumbers->pop();
      }
      ASS(curr);
      break;
    }
    if(!curr) {
      //there are no other alternatives
      return false;
    }
    if(!_subst.matchNext(currSpecVar, curr->term, sibilingsRemain)) {	//[1]
      //match unsuccessful, try next alternative
      curr=0;
      if(!sibilingsRemain && _alternatives->isNonEmpty()) {
        _subst.backtrack();
      }
      continue;
    }
    while(!curr->isLeaf() && curr->algorithm()==UNSORTED_LIST && static_cast<UArrIntermediateNode*>(curr)->_size==1) {
      //a node with only one child, we don't need to bother with backtracking here.
      unsigned specVar=static_cast<UArrIntermediateNode*>(curr)->childVar;
      curr=static_cast<UArrIntermediateNode*>(curr)->_nodes[0];
      ASS(curr);
      ASSERT_VALID(*curr);
      if(!_subst.matchNext(specVar, curr->term, false)) {
        //matching failed, let's go back to the node, that had multiple children
        //_subst.backtrack();
        if(sibilingsRemain || _alternatives->isNonEmpty()) {
          //this backtrack can happen for two different reasons and have two different meanings:
          //either matching at [1] was separated from the previous one and we're backtracking it,
          //or it was not, which means it had no sibilings and we're backtracking from its parent.
          _subst.backtrack();
        }
        curr=0;
        goto main_loop_start;
      }
    }
    if(curr->isLeaf()) {
      //we've found a leaf
      _ldIterator=static_cast<Leaf*>(curr)->allChildren();
      _inLeaf=true;
      _subst.onLeafEntered(); //we reset the bindings cache
      return true;
    }

    //let's go to the first child
    sibilingsRemain=enterNode(curr);
    if(curr==0 && _alternatives->isNonEmpty()) {
      _subst.backtrack();
    }
  }
}

/**
 * Enter into node @b curr, modifying the value of @b curr
 *
 * This means that if @b curr has any admissible children, assign one of them
 * into @b curr, and push special variable that corresponds to it into
 * @b _specVarNumbers.
 *
 * If there are more than one admissible child, push a pointer that will allow
 * retrieving the others into @b _alternatives and node type of the current parent
 * into @b _nodeTypes (this information will allow us later to interpret the
 * pointer correctly). Also return true in this case. If there is none or only
 * one admissible child, return false.
 */
bool SubstitutionTree::FastInstancesIterator::enterNode(Node*& curr)
{
  CALL("SubstitutionTree::FastInstancesIterator::enterNode");
  ASSERT_VALID(*curr);
  ASS(!curr->isLeaf());

  IntermediateNode* inode=static_cast<IntermediateNode*>(curr);
  NodeAlgorithm currType=inode->algorithm();

  TermList query;
  InstMatcher::TermSpec querySpec;
  //here we are interested only in the top functor or the fact that the query is a variable
  //so we can discard the information about term origin
  if(_subst.findSpecVarBinding(inode->childVar, querySpec)) {
    query=querySpec.t;
  }
  else {
    query.makeVar(0);//just an arbitrary variable so that anything will match
  }

  curr=0;

  if(currType==UNSORTED_LIST) {
    Node** nl=static_cast<UArrIntermediateNode*>(inode)->_nodes;
    ASS(*nl); //inode is not empty
    bool noAlternatives=false;
    if(query.isTerm()) {
      unsigned bindingFunctor=query.term()->functor();
      //let's skip terms that don't have the same top functor...
      while(*nl && (!(*nl)->term.isTerm() || (*nl)->term.term()->functor()!=bindingFunctor)) {
        nl++;
      }

      if(*nl) {
        //we've found the term with the same top functor
        ASS_EQ((*nl)->term.term()->functor(),bindingFunctor);
        curr=*nl;
        noAlternatives=true; //there is at most one term with each top functor
      }
    } else {
      ASS(query.isVar());
      //everything is matched by a variable
      curr=*nl;
      nl++;
    }

    if(curr) {
      _specVarNumbers->push(inode->childVar);
    }
    if(*nl && !noAlternatives) {
      _alternatives->push(nl);
      _nodeTypes->push(currType);
      return true;
    }
  } else {
    ASS_EQ(currType, SKIP_LIST);
    auto nl=static_cast<SListIntermediateNode*>(inode)->_nodes.listLike();
    ASS(nl); //inode is not empty
    if(query.isTerm()) {
      //only term with the same top functor will be matched by a term
      Node** byTop=inode->childByTop(query.top(), false);
      if(byTop) {
        curr=*byTop;
      }
      nl=0;
    }
    else {
      ASS(query.isVar());
      //everything is matched by a variable
      curr=nl->head();
      nl=nl->tail();
    }

    if(curr) {
      _specVarNumbers->push(inode->childVar);
    }
    if(nl) {
      _alternatives->push(nl);
      _nodeTypes->push(currType);
      return true;
    }
  }
  return false;
}


}
