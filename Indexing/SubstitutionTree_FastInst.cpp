/**
 * @file SubstitutionTree_FastIterator.cpp
 * Implements class SubstitutionTree::FastIterator, its child classes
 * and some auxiliary classes.
 */

#include "Lib/Allocator.hpp"
#include "Lib/Recycler.hpp"

#include "Kernel/Matcher.hpp"
#include "Kernel/SubstHelper.hpp"

#include "SubstitutionTree.hpp"

#undef LOGGING
#define LOGGING 1

namespace Indexing
{

/**
 * Class that supports matching operations required by
 * retrieval of generalizations in substitution trees.
 */
class SubstitutionTree::GenMatcher
{
public:
  GenMatcher()
  : _boundVars(256)
  {
    Recycler::get(_specVars);
    Recycler::get(_bindings);

    _specVars->reset();
    _bindings->reset();
  }

  virtual ~GenMatcher()
  {
    Recycler::release(_specVars);
    Recycler::release(_bindings);
  }


  /**
   * Bind special variable @b var to @b term
   *
   * This method should be called only before any calls to @b matchNext()
   * and @b backtrack().
   */
  void bindSpecialVar(unsigned var, TermList term)
  {
    ASSERT_VALID(term);
    LOG("###spec var init bound: "<<var<<"  t: "<<term);

    ALWAYS(_specVars->insert(var,term));
  }

  bool isSpecVarBound(unsigned specVar)
  {
    return _specVars->find(specVar);
  }

  /** Return term bound to special variable @b specVar */
  TermList getSpecVarBinding(unsigned specVar)
  {
    TermList res=_specVars->get(specVar);
    ASSERT_VALID(res);
    return res;
  }

  virtual bool matchNext(unsigned specVar, TermList nodeTerm, bool separate=true) = 0;

  virtual void backtrack();
  virtual bool tryBacktrack();
  virtual ResultSubstitutionSP getSubstitution(Renaming* resultNormalizer);

  int getBSCnt()
  {
    int res=0;
    VarStack::Iterator vsit(_boundVars);
    while(vsit.hasNext()) {
	if(vsit.next()==BACKTRACK_SEPARATOR) {
	  res++;
	}
    }
    return res;
  }

protected:
  typedef DHMap<unsigned, TermList> BindingMap;
  static const unsigned BACKTRACK_SEPARATOR=0xFFFFFFFF;

  VarStack _boundVars;

  BindingMap* _specVars;

  struct Binder;
  struct Applicator;
  class Substitution;

  /**
   * Inheritors must ensure that the map can take at least @b _maxVar
   * as a key
   */
  BindingMap* _bindings;

};

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
  : _parent(parent) {}
  /**
   * Ensure variable @b var is bound to @b term. Return false iff
   * it is not possible. If a new binding was creater, push @b var
   * onto parent's @b _boundVars stack.
   */
  bool bind(unsigned var, TermList term)
  {
    LOGV(var);

    TermList* aux;
    if(_parent->_bindings->getValuePtr(var,aux,term)) {
      _parent->_boundVars.push(var);
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
    ASSERT_VALID(term);
    LOG("###spec var bound: "<<var<<"  t: "<<(term));

    ALWAYS(_parent->_specVars->insert(var,term));
  }
private:
  GenMatcher* _parent;
};

struct SubstitutionTree::GenMatcher::Applicator
{
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

  TermList applyToBoundResult(TermList t)
  { return SubstHelper::apply(t, *getApplicator()); }

  Literal* applyToBoundResult(Literal* lit)
  { return SubstHelper::apply(lit, *getApplicator()); }

  bool isIdentityOnQueryWhenResultBound() {return true;}
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

/**
 * Undo one call to the @b matchNext method with separate param
 * set to @b true and all other @b matchNext calls that were joined to it.
 */
void SubstitutionTree::GenMatcher::backtrack()
{
  CALL("SubstitutionTree::FastMatcher::backtrack");

  for(;;) {
    unsigned boundVar=_boundVars.pop();
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
  CALL("SubstitutionTree::FastMatcher::tryBacktrack");

  while(_boundVars.isNonEmpty()) {
    unsigned boundVar=_boundVars.pop();
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



/**
 * @b nextSpecVar is the first unassigned special variable. Is being used
 * 	to determine size of array, that stores special variable bindings.
 * 	(To maximize performance, a DArray object is being used instead
 * 	of hash map.)
 * If @b reversed If true, parameters of supplied binary literal are
 * 	reversed. (useful for retrieval commutative terms)
 */
SubstitutionTree::FastGeneralizationIterator2::FastGeneralizationIterator2(SubstitutionTree* parent, Node* root,
	Term* query, bool retrieveSubstitution, bool reversed, GenMatcher* subst)
: _literalRetrieval(query->isLiteral()), _retrieveSubstitution(retrieveSubstitution),
  _subst(subst), _ldIterator(LDIterator::getEmpty()), _tree(parent)
{
  CALL("SubstitutionTree::FastGeneralizationsIterator::FastGeneralizationsIterator");
  ASS(root);
  ASS(!root->isLeaf());

#if VDEBUG
  _tree->_iteratorCnt++;
#endif

  if(reversed) {
    createReversedInitialBindings(query);
  } else {
    createInitialBindings(query);
  }
}

SubstitutionTree::FastGeneralizationIterator2::~FastGeneralizationIterator2()
{
#if VDEBUG
  _tree->_iteratorCnt--;
#endif
  delete _subst;
}


void SubstitutionTree::FastGeneralizationIterator2::createInitialBindings(Term* t)
{
  CALL("SubstitutionTree::FastIterator::createInitialBindings");

  TermList* args=t->args();
  int nextVar = 0;
  while (! args->isEmpty()) {
    unsigned var = nextVar++;
    _subst->bindSpecialVar(var,*args);
    args = args->next();
  }
}

/**
 * For a binary comutative query literal, create initial bindings,
 * where the order of special variables is reversed.
 */
void SubstitutionTree::FastGeneralizationIterator2::createReversedInitialBindings(Term* t)
{
  CALL("SubstitutionTree::FastIterator::createReversedInitialBindings");
  ASS(t->isLiteral());
  ASS(t->commutative());
  ASS_EQ(t->arity(),2);

  _subst->bindSpecialVar(1,*t->nthArgument(0));
  _subst->bindSpecialVar(0,*t->nthArgument(1));
}

bool SubstitutionTree::FastGeneralizationIterator2::hasNext()
{
  CALL("SubstitutionTree::FastIterator::hasNext");

  while(!_ldIterator.hasNext() && findNextLeaf()) {}
  return _ldIterator.hasNext();
}

SubstitutionTree::QueryResult SubstitutionTree::FastGeneralizationIterator2::next()
{
  CALL("SubstitutionTree::FastIterator::next");

  while(!_ldIterator.hasNext() && findNextLeaf()) {}
  ASS(_ldIterator.hasNext());
  LeafData& ld=_ldIterator.next();

  if(_retrieveSubstitution) {
    _resultNormalizer.reset();
    if(_literalRetrieval) {
      _resultNormalizer.normalizeVariables(ld.literal);
    } else {
      _resultNormalizer.normalizeVariables(ld.term);
    }

    return QueryResult(&ld,
	    _subst->getSubstitution(&_resultNormalizer));
  } else {
    return QueryResult(&ld, ResultSubstitutionSP());
  }
}

//////////////////////////////////////////////
// Instance retrieval
//////////////////////////////////////////////

/**
 * Class that supports matching operations required by
 * retrieval of generalizations in substitution trees.
 */
class SubstitutionTree::InstMatcher
: public GenMatcher
{
public:
  CLASS_NAME("SubstitutionTree::InstMatcher");
  USE_ALLOCATOR(InstMatcher);

  virtual bool matchNext(unsigned specVar, TermList nodeTerm, bool separate=true);

  virtual ResultSubstitutionSP getSubstitution(Renaming* resultNormalizer)
  { NOT_IMPLEMENTED; }

};


/**
 * Match @b nodeTerm to term in the special variable @b specVar.
 * If @b separate is true, join this match with the previous one
 * on backtracking stack, so they will be undone both by one
 * call to the backtrack() method.
 */
bool SubstitutionTree::InstMatcher::matchNext(unsigned specVar, TermList nodeTerm, bool separate)
{
  CALL("SubstitutionTree::InstMatcher::matchNext");

  if(separate) {
    _boundVars.push(BACKTRACK_SEPARATOR);
  }

  TermList queryTerm;
  if(!_specVars->find(specVar, queryTerm)) {
    //special variable was not bound, this means we can match anything
    LOGV("1 from unmatched spec var");
    return true;
  }

  ASSERT_VALID(queryTerm);
  LOG("matching q: "<<queryTerm.toString()<<"  n: "<<nodeTerm.toString());

  bool success;
  if(queryTerm.isTerm()) {
    Term* qt=queryTerm.term();
    if(qt->shared() && qt->ground()) {
      //ground terms match only iff they're equal
      success = nodeTerm==queryTerm;
    } else {
      Binder binder(this);
      ASS(qt->arity()>0);

      success = nodeTerm.isTerm() && nodeTerm.term()->functor()==qt->functor() &&
	MatchingUtils::matchArgs(qt, nodeTerm.term(), binder);
    }
  } else {
    ASS_METHOD(queryTerm,isOrdinaryVar());
    unsigned var=queryTerm.var();
    Binder binder(this);
    success=binder.bind(var,nodeTerm);
  }

  if(!success) {
    //if this matching was joined to the previous one, we don't
    //have to care about unbinding as caller will do this by calling
    //backtrack for the matching we're joined to.
    if(separate) {
      //we have to unbind ordinary variables, that were bound.
      for(;;) {
	unsigned boundVar=_boundVars.pop();
	if(boundVar==BACKTRACK_SEPARATOR) {
	  break;
	}
	_bindings->remove(boundVar);
      }
    }
  }
  LOGV(success);
  return success;
}

/**
 * @b nextSpecVar is the first unassigned special variable. Is being used
 * 	to determine size of array, that stores special variable bindings.
 * 	(To maximize performance, a DArray object is being used instead
 * 	of hash map.)
 * If @b reversed If true, parameters of supplied binary literal are
 * 	reversed. (useful for retrieval commutative terms)
 */
SubstitutionTree::FastInstancesIterator::FastInstancesIterator(
	SubstitutionTree* parent, Node* root,
	Term* query, bool retrieveSubstitution, bool reversed)
: FastGeneralizationIterator2(parent, root, query, retrieveSubstitution, reversed,
    new InstMatcher),
  _root(root), _inLeaf(false), _alternatives(64), _specVarNumbers(64), _nodeTypes(64)
{
  CALL("SubstitutionTree::FastInstancesIterator::FastGeneralizationsIterator");
  LOG("-----------new iterator--------------");
  LOGV(*query);
}

/**
 * Find next leaf, that contains instances of the query
 * term. If there is no such, return false.
 */
bool SubstitutionTree::FastInstancesIterator::findNextLeaf()
{
  CALL("SubstitutionTree::FastInstancesIterator::findNextLeaf");
  LOG("findNextLeaf");

  Node* curr;
  bool sibilingsRemain;
  if(_inLeaf) {
    if(_alternatives.isEmpty()) {
      return false;
    }
    _subst->backtrack();
    _inLeaf=false;
    curr=0;
  } else {
    if(!_root) {
      //If we aren't in a leaf and the findNextLeaf method has already been called,
      //it means that we're out of leafs.
      return false;
    }
    LOG("root");
    curr=_root;
    _root=0;
    sibilingsRemain=enterNode(curr);
  }
  for(;;) {
main_loop_start:
    unsigned currSpecVar;

    if(curr) {
      if(sibilingsRemain) {
	ASS(_nodeTypes.top()!=UNSORTED_LIST || *static_cast<Node**>(_alternatives.top()));
	currSpecVar=_specVarNumbers.top();
      } else {
	currSpecVar=_specVarNumbers.pop();
      }
    }
    //let's find a node we haven't been to...
    while(curr==0 && _alternatives.isNonEmpty()) {
      void* currAlt=_alternatives.pop();
      if(!currAlt) {
	//there's no alternative at this level, we have to backtrack
	_nodeTypes.pop();
	_specVarNumbers.pop();
	if(_alternatives.isNonEmpty()) {
	  _subst->backtrack();
	}
	continue;
      }

      NodeAlgorithm parentType=_nodeTypes.top();

      //the fact that we have alternatives means that here we are
      //matching by a variable (as there is always at most one child
      //for matching by term)
      if(parentType==UNSORTED_LIST) {
	Node** alts=static_cast<Node**>(currAlt);
	curr=*(alts++);
	if(*alts) {
	  _alternatives.push(alts);
	  sibilingsRemain=true;
	} else {
	  sibilingsRemain=false;
	}
      } else {
	ASS_EQ(parentType,SKIP_LIST)
	NodeList* alts=static_cast<NodeList*>(currAlt);
	ASS(alts);

	NodeList::Iterator ait(alts);
	while(ait.hasNext()){
	  Node* ln=ait.next();
	  LOGV(ln->term.toString());
	}
	LOG("--end of list--");

	curr=alts->head();
	if(alts->tail()) {
	  _alternatives.push(alts->tail());
	  sibilingsRemain=true;
	} else {
	  sibilingsRemain=false;
	}
      }

      if(sibilingsRemain) {
	currSpecVar=_specVarNumbers.top();
      } else {
	_nodeTypes.pop();
	currSpecVar=_specVarNumbers.pop();
      }
      ASS(curr);
      break;
    }
    if(!curr) {
      //there are no other alternatives
      return false;
    }
    if(!_subst->matchNext(currSpecVar, curr->term, sibilingsRemain)) {	//[1]
      //match unsuccessful, try next alternative
      LOG("match fail");
      curr=0;
      if(!sibilingsRemain && _alternatives.isNonEmpty()) {
	_subst->backtrack();
      }
      continue;
    }
    LOG("match ok");
    while(!curr->isLeaf() && curr->algorithm()==UNSORTED_LIST && static_cast<UArrIntermediateNode*>(curr)->_size==1) {
      //a node with only one child, we don't need to bother with backtracking here.
      unsigned specVar=static_cast<UArrIntermediateNode*>(curr)->childVar;
      curr=static_cast<UArrIntermediateNode*>(curr)->_nodes[0];
      ASS(curr);
      ASSERT_VALID(*curr);
      if(!_subst->matchNext(specVar, curr->term, false)) {
	//matching failed, let's go back to the node, that had multiple children
	//_subst->backtrack();
	if(sibilingsRemain || _alternatives.isNonEmpty()) {
	  //this backtrack can happen for two different reasons and have two different meanings:
	  //either matching at [1] was separated from the previous one and we're backtracking it,
	  //or it was not, which means it had no sibilings and we're backtracking from its parent.
	  _subst->backtrack();
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
    if(curr==0 && _alternatives.isNonEmpty()) {
      _subst->backtrack();
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
  LOG("enterNode");
  ASSERT_VALID(*curr);
  ASS(!curr->isLeaf());

  IntermediateNode* inode=static_cast<IntermediateNode*>(curr);
  NodeAlgorithm currType=inode->algorithm();

  LOGV(inode->childVar);
  bool isSpecVarBound=_subst->isSpecVarBound(inode->childVar);

  TermList query;
  if(isSpecVarBound) {
    query=_subst->getSpecVarBinding(inode->childVar);
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
      ASS(query.isOrdinaryVar());
      //everything is matched by a variable
      curr=*nl;
      nl++;
    }

    if(curr) {
      _specVarNumbers.push(inode->childVar);
    }
    if(*nl && !noAlternatives) {
      _alternatives.push(nl);
      _nodeTypes.push(currType);
      LOG("have alts u");
      return true;
    }
  } else {
    NodeList* nl;
    ASS_EQ(currType, SKIP_LIST);
    nl=static_cast<SListIntermediateNode*>(inode)->_nodes.toList();
    ASS(nl); //inode is not empty
    if(query.isTerm()) {
      //only term with the same top functor will be matched by a term
      Node** byTop=inode->childByTop(query, false);
      if(byTop) {
	curr=*byTop;
      }
      nl=0;
    }
    else {
      ASS(query.isOrdinaryVar());
      //everything is matched by a variable
      curr=nl->head();
      nl=nl->tail();
    }

    if(curr) {
      _specVarNumbers.push(inode->childVar);
    }
    if(nl) {
      _alternatives.push(nl);
      _nodeTypes.push(currType);
      LOG("have alts s");
      return true;
    }
  }
  return false;
}


}
