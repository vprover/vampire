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
 * @file SubstitutionTree_FastGen.cpp
 * Implements class SubstitutionTree::FastGen, its child classes
 * and some auxiliary classes.
 */

#include "Lib/Allocator.hpp"
#include "Lib/Recycled.hpp"

#include "Kernel/Matcher.hpp"
#include "Kernel/SubstHelper.hpp"

#include "SubstitutionTree.hpp"

namespace Indexing
{



const unsigned SubstitutionTree::GenMatcher::BACKTRACK_SEPARATOR;

/**
 * Binding structure to be passed to the @b MatchingUtils::matchArgs
 * method.
 */
struct SubstitutionTree::GenMatcher::Binder
{
  /**
   * Create Binder structure for @b _parent. Use @b newSpecVars
   * to store numbers of special variables, that were bound by
   * this object.
   */
  inline
  Binder(GenMatcher* parent)
  : _parent(parent), _maxVar(parent->_maxVar) {}
  /**
   * Ensure variable @b var is bound to @b term. Return false iff
   * it is not possible. If a new binding was creater, push @b var
   * onto parent's @b _boundVars stack.
   */
  bool bind(unsigned var, TermList term)
  {
    if(var > _maxVar) {
      return false;
    }
    TermList* aux;
    if(_parent->_bindings->getValuePtr(var,aux,term)) {
      _parent->_boundVars->push(var);
      return true;
    } else {
      return *aux==term;
    }
  }
  /**
   * Bind special variable @b var to @b term, and push @b var
   * onto @b _newSpecVars stack.
   */
  inline
  void specVar(unsigned var, TermList term)
  {
    (*_parent->_specVars)[var]=term;
  }
private:
  GenMatcher* _parent;
  /**
   * Maximal number of boundable ordinary variable. If binding
   * bigger variable is attempted, it fails.
   */
  unsigned _maxVar;
};

struct SubstitutionTree::GenMatcher::Applicator
{
  CLASS_NAME(SubstitutionTree::GenMatcher::Applicator);
  USE_ALLOCATOR(SubstitutionTree::GenMatcher::Applicator); 

  inline
  Applicator(GenMatcher* parent, Renaming* resultNormalizer)
  : _parent(parent), _resultNormalizer(resultNormalizer) {}
  TermList apply(unsigned var)
  {
    TermList* cacheEntry;
    if(_cache.getValuePtr(var,cacheEntry)) {
      ASS(_resultNormalizer->contains(var));
      unsigned nvar=_resultNormalizer->get(var);
      ASS(_parent->_bindings->find(nvar));
      *cacheEntry=_parent->_bindings->get(nvar);
    }
    return *cacheEntry;
  }
private:
  GenMatcher* _parent;
  Renaming* _resultNormalizer;
  BindingMap _cache;
};

class SubstitutionTree::GenMatcher::Substitution
: public ResultSubstitution
{
public:
  CLASS_NAME(SubstitutionTree::GenMatcher::Substitution);
  USE_ALLOCATOR(SubstitutionTree::GenMatcher::Substitution);
  
  Substitution(GenMatcher* parent, Renaming* resultNormalizer)
  : _parent(parent), _resultNormalizer(resultNormalizer),
  _applicator(0)
  {}
  ~Substitution()
  {
    if(_applicator) {
      delete _applicator;
    }
  }

  TermList applyToBoundResult(TermList t) override
  { return SubstHelper::apply(t, *getApplicator()); }

  Literal* applyToBoundResult(Literal* lit) override
  { return SubstHelper::apply(lit, *getApplicator()); }

  bool isIdentityOnQueryWhenResultBound() override
  { return true; }

  virtual void output(std::ostream& out) const final override 
  { out << "GenMatcher::Substitution(<output unimplemented>)"; }
private:
  Applicator* getApplicator()
  {
    if(!_applicator) {
      _applicator=new Applicator(_parent, _resultNormalizer);
    }
    return _applicator;
  }

  GenMatcher* _parent;
  Renaming* _resultNormalizer;
  Applicator* _applicator;
};

bool SubstitutionTree::GenMatcher::matchNext(unsigned specVar, TermList nodeTerm, bool separate)
{
  CALL("SubstitutionTree::GenMatcher::matchNext");

  if(separate) {
    _boundVars->push(BACKTRACK_SEPARATOR);
  }

  TermList queryTerm=(*_specVars)[specVar];
  ASSERT_VALID(queryTerm);

  return matchNextAux(queryTerm, nodeTerm, separate);
}


/**
 * Match special variable, that is about to be matched next during
 * iterator's traversal through the tree, to @b nodeTerm.
 * If @b separate If true, join this match with the previous one
 * on backtracking stack, so they will be undone both by one
 * call to the backtrack() method.
 */
bool SubstitutionTree::GenMatcher::matchNextAux(TermList queryTerm, TermList nodeTerm, bool separate)
{
  CALL("SubstitutionTree::GenMatcher::matchNextAux");

  bool success;

  if(nodeTerm.isTerm()) {
    Term* nt=nodeTerm.term();
    if(nt->shared() && nt->ground()) {
      //ground terms match only iff they're equal
      success = nodeTerm==queryTerm;
    } else {
      Binder binder(this);
      ASS(nt->arity()>0);

      success = queryTerm.isTerm() && queryTerm.term()->functor()==nt->functor() &&
                  MatchingUtils::matchArgs(nt, queryTerm.term(), binder);
    }
  } else {
    ASS_METHOD(nodeTerm,isOrdinaryVar());
    unsigned var=nodeTerm.var();
    Binder binder(this);
    success=binder.bind(var,queryTerm);
  }

  if(!success) {
    //if this matching was joined to the previous one, we don't
    //have to care about unbinding as caller will do this by calling
    //backtrack for the matching we're joined to.
    if(separate) {
      //we have to unbind ordinary variables, that were bound.
      for(;;) {
        unsigned boundVar = _boundVars->pop();
        if(boundVar==BACKTRACK_SEPARATOR) {
          break;
        }
        _bindings->remove(boundVar);
      }
    }
  }

  return success;
}

/**
 * Undo one call to the @b matchNext method with separate param
 * set to @b true and all other @b matchNext calls that were joined to it.
 */
void SubstitutionTree::GenMatcher::backtrack()
{
  CALL("SubstitutionTree::GenMatcher::backtrack");

  for(;;) {
    unsigned boundVar = _boundVars->pop();
    if(boundVar==BACKTRACK_SEPARATOR) {
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
bool SubstitutionTree::GenMatcher::tryBacktrack()
{
  CALL("SubstitutionTree::GenMatcher::tryBacktrack");

  while(_boundVars->isNonEmpty()) {
    unsigned boundVar = _boundVars->pop();
    if(boundVar==BACKTRACK_SEPARATOR) {
      return true;
    }
    _bindings->remove(boundVar);
  }
  return false;
}


ResultSubstitutionSP SubstitutionTree::GenMatcher::getSubstitution(
	Renaming* resultNormalizer)
{
  return ResultSubstitutionSP(
	  new Substitution(this, resultNormalizer));
}


bool SubstitutionTree::FastGeneralizationsIterator::hasNext()
{
  CALL("SubstitutionTree::FastGeneralizationsIterator::hasNext");

  while(!_ldIterator.hasNext() && findNextLeaf()) {}
  return _ldIterator.hasNext();
}

SubstitutionTree::QueryResultIter SubstitutionTree::FastGeneralizationsIterator::next()
{
  CALL("SubstitutionTree::FastGeneralizationsIterator::next");

  while(!_ldIterator.hasNext() && findNextLeaf()) {}
  ASS(_ldIterator.hasNext());
  auto ld = _ldIterator.next();

  if(_retrieveSubstitution) {
    _resultNormalizer->reset();
    if(_literalRetrieval) {
      _resultNormalizer->normalizeVariables(ld->literal);
    } else {
      _resultNormalizer->normalizeVariables(ld->term);
    }

    // TODO update this once we make matching iterators templated on matching algorithm
    // or remove altogether if we go with Joe's refactor
    return pvi(getSingletonIterator(QueryResult(ld,_subst.getSubstitution(&*_resultNormalizer))));
  } else {
    return pvi(getSingletonIterator(QueryResult(ld, ResultSubstitutionSP())));
  }
}

/**
 * Find next leaf, that contains generalizations of the query
 * term. If there is no such, return false.
 */
bool SubstitutionTree::FastGeneralizationsIterator::findNextLeaf()
{
  CALL("SubstitutionTree::FastGeneralizationsIterator::findNextLeaf");

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
        currSpecVar=_specVarNumbers->top();
      } else {
        currSpecVar=_specVarNumbers->pop();
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

      NodeAlgorithm parentType=_nodeTypes->top();

      //proper term nodes that we want to enter don't appear
      //on _alternatives stack (as we always enter them first)
      if(parentType==UNSORTED_LIST) {
        Node** alts=static_cast<Node**>(currAlt);
        while(*alts && !(*alts)->term.isVar()) {
          alts++;
        }
        curr=*(alts++);
        while(*alts && !(*alts)->term.isVar()) {
          alts++;
        }
        if(*alts) {
          _alternatives->push(alts);
          sibilingsRemain=true;
        } else {
          sibilingsRemain=false;
        }
      } else {
        ASS_EQ(parentType,SKIP_LIST)
        auto alts = static_cast<SListIntermediateNode::NodeSkipList::Node *>(currAlt);
        if(alts->head()->term.isVar()) {
          curr=alts->head();
          if(alts->tail() && alts->tail()->head()->term.isVar()) {
            _alternatives->push(alts->tail());
            sibilingsRemain=true;
          } else {
            sibilingsRemain=false;
          }
        }
      }

      if(sibilingsRemain) {
        currSpecVar=_specVarNumbers->top();
      } else {
        _nodeTypes->pop();
        currSpecVar=_specVarNumbers->pop();
      }
      if(curr) {
        break;
      }
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
        //_subst->backtrack();
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
bool SubstitutionTree::FastGeneralizationsIterator::enterNode(Node*& curr)
{
  IntermediateNode* inode=static_cast<IntermediateNode*>(curr);
  NodeAlgorithm currType=inode->algorithm();

  TermList binding = _subst.getSpecVarBinding(inode->childVar);
  curr=0;

  if(currType==UNSORTED_LIST) {
    Node** nl=static_cast<UArrIntermediateNode*>(inode)->_nodes;
    if(binding.isTerm()) {
      unsigned bindingFunctor=binding.term()->functor();
      //let's first skip proper term nodes at the beginning...
      while(*nl && (*nl)->term.isTerm()) {
        //...and have the one that interests us, if we encounter it.
        if(!curr && (*nl)->term.term()->functor()==bindingFunctor) {
          curr=*nl;
        }
        nl++;
      }
      if(!curr && *nl) {
        //we've encountered a variable node, but we still have to check, whether
        //the one proper term node, that interests us, isn't here
        Node** nl2=nl+1;
        while(*nl2) {
          if((*nl2)->term.isTerm() && (*nl2)->term.term()->functor()==bindingFunctor) {
            curr=*nl2;
            break;
          }
          nl2++;
        }
      }
    } else {
      //let's first skip proper term nodes at the beginning
      while(*nl && (*nl)->term.isTerm()) {
        nl++;
      }
    }
    if(!curr && *nl) {
      curr=*(nl++);
      while(*nl && (*nl)->term.isTerm()) {
	nl++;
      }
    }
    if(curr) {
      _specVarNumbers->push(inode->childVar);
    }
    if(*nl) {
      _alternatives->push(nl);
      _nodeTypes->push(currType);
      return true;
    }
  } else {
    ASS_EQ(currType, SKIP_LIST);
    auto nl=static_cast<SListIntermediateNode*>(inode)->_nodes.listLike();
    if(binding.isTerm()) {
      Node** byTop=inode->childByTop(binding.top(), false);
      if(byTop) {
	curr=*byTop;
      }
    }
    if(!curr && nl->head()->term.isVar()) {
      curr=nl->head();
      nl=nl->tail();
    }
    //in SkipList nodes variables are only at the beginning
    //(so if there aren't any, there aren't any at all)
    if(nl && nl->head()->term.isTerm()) {
      nl=0;
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
