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
#include "Lib/Recycler.hpp"

#include "Kernel/Matcher.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/TermIterators.hpp"

#include "SubstitutionTree.hpp"

namespace Indexing
{

/**
 * Class that supports matching operations required by
 * retrieval of generalizations in substitution trees.
 */
class SubstitutionTree::InstMatcher
{
public:
  void reset()
  {
    _boundVars.reset();
    _bindings.reset();
    _derefBindings.reset();
  }

  CLASS_NAME(SubstitutionTree::InstMatcher);
  USE_ALLOCATOR(InstMatcher);

  struct TermSpec
  {
    TermSpec() : q(false) {
    #if VDEBUG
      t.makeEmpty();
    #endif
    }
    TermSpec(bool q, TermList t)
    : q(q), t(t)
    {
      CALL("SubstitutionTree::InstMatcher::TermSpec::TermSpec");

      //query does not contain special vars
      ASS(!q || !t.isTerm() || t.term()->shared());
      ASS(!q || !t.isSpecialVar());
    }

    vstring toString()
    {
      CALL("SubstitutionTree::InstMatcher::TermSpec::toString");
      return (q ? "q|" : "n|")+t.toString();
    }

    /**
     * Return true if the @b t field can be use as a binding for a query
     * term variable in the retrieved substitution
     */
    bool isFinal()
    {
      //the fact that a term is shared means it does not contain any special variables
      return q
  	? (t.isTerm() && t.term()->ground())
  	: (t.isOrdinaryVar() || (t.isTerm() && t.term()->shared()) );
    }

    bool q;
    TermList t;
  };

  /**
   * Bind special variable @b var to @b term
   *
   * This method should be called only before any calls to @b matchNext()
   * and @b backtrack().
   */
  void bindSpecialVar(unsigned var, TermList term)
  {
    CALL("SubstitutionTree::InstMatcher::bindSpecialVar");
    ASS_EQ(getBSCnt(), 0);

    ALWAYS(_bindings.insert(TermList(var,true),TermSpec(true,term)));
  }

  bool isSpecVarBound(unsigned specVar)
  {
    return _bindings.find(TermList(specVar,true));
  }

  /** Return term bound to special variable @b specVar */
  TermSpec getSpecVarBinding(unsigned specVar)
  {
    TermSpec res=_bindings.get(TermList(specVar,true));

    return res;
  }

  bool findSpecVarBinding(unsigned specVar, TermSpec& res)
  {
    return _bindings.find(TermList(specVar,true), res);
  }

  bool matchNext(unsigned specVar, TermList nodeTerm, bool separate=true);
  bool matchNextAux(TermList queryTerm, TermList nodeTerm, bool separate=true);

  void backtrack();
  bool tryBacktrack();
  ResultSubstitutionSP getSubstitution(Renaming* resultDenormalizer);

  int getBSCnt()
  {
    int res=0;
    TermStack::Iterator vsit(_boundVars);
    while(vsit.hasNext()) {
      if(vsit.next().isEmpty()) {
	res++;
      }
    }
    return res;
  }

  void onLeafEntered()
  {
    _derefBindings.reset();
  }

private:

  class Substitution;

  TermList derefQueryBinding(unsigned var);

  bool isBound(TermList var)
  {
    CALL("SubstitutionTree::InstMatcher::isBound");
    ASS(var.isVar());

    return _bindings.find(var);
  }
  void bind(TermList var, TermSpec trm)
  {
    CALL("SubstitutionTree::InstMatcher::bind");
    ASS(!var.isOrdinaryVar() || !trm.q); //we do not bind ordinary vars to query terms

    ALWAYS(_bindings.insert(var, trm));
    _boundVars.push(var);
  }

  TermSpec deref(TermList var);

  typedef DHMap<TermList, TermSpec> BindingMap;
  typedef Stack<TermList> TermStack;

  /** Stacks of bindings made on each backtrack level. Backtrack
   * levels are separated by empty terms. */
  TermStack _boundVars;

  BindingMap _bindings;

  /**
   * A cache for bindings of variables to result terms
   *
   * The map is reset whenever we enter a new leaf
   */
  DHMap<TermList,TermList> _derefBindings;

  struct DerefTask
  {
    DerefTask(TermList var) : var(var) { trm.t.makeEmpty(); }
    DerefTask(TermList var, TermSpec trm) : var(var), trm(trm) {}
    TermList var;
    TermSpec trm;
    bool buildDerefTerm() { return trm.t.isNonEmpty(); };
  };

  struct DerefApplicator
  {
    DerefApplicator(InstMatcher* im, bool query) : query(query), im(im) {}
    TermList apply(unsigned var)
    {
      CALL("SubstitutionTree::InstMatcher::DerefApplicator::apply");
      if(query) {
	return im->_derefBindings.get(TermList(var, false));
      }
      else {
	return TermList(var, false);
      }
    }
    TermList applyToSpecVar(unsigned specVar)
    {
      CALL("SubstitutionTree::InstMatcher::DerefApplicator::applyToSpecVar");
      ASS(!query);

      return im->_derefBindings.get(TermList(specVar, true));
    }
  private:
    bool query;
    InstMatcher* im;
  };
};

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

  bool matchSorts(TermList base, TermList instance) override
  {
    CALL("SubstitutionTree::InstMatcher::Substitution::matchSorts");

    return _parent->matchNextAux(base, instance, false);
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
    if(_derefBindings.find(tvar, val)) {
      return val;
    }
    //only bound values can be passed to this function
    ALWAYS(_bindings.find(tvar, varBinding));

    if(varBinding.isFinal()) {
      ALWAYS(_derefBindings.insert(tvar, varBinding.t));
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

      if(_derefBindings.find(bvar, derefBoundTerm)) {
	ALWAYS(_derefBindings.insert(tvar, derefBoundTerm));
      }

      ALWAYS(_bindings.find(bvar,varBinding));
    }
    if(varBinding.isFinal()) {
      ALWAYS(_derefBindings.insert(tvar, varBinding.t));
      goto next_loop;
    }
    {
      ASS(varBinding.t.isTerm());
      toDo.push(DerefTask(tvar, varBinding));
      VariableIterator vit(varBinding.t);
      while(vit.hasNext()) {
	TermList btv=vit.next(); //bound term variable
	if(varBinding.q || btv.isSpecialVar()) {
	  ASS(_bindings.find(btv));
	  if(!_derefBindings.find(btv)) {
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
      ALWAYS(_derefBindings.insert(tvar, derefTerm));
    }
    if(toDo.isEmpty()) {
      break;
    }
    tvar=toDo.pop().var;
    ALWAYS(_bindings.find(tvar, varBinding));
  };
  return _derefBindings.get(tvar0);
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
    if(!_bindings.find(var, res)) {
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
    TermList boundVar=_boundVars.pop();
    if(boundVar.isEmpty()) {
      break;
    }
    _bindings.remove(boundVar);
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

  while(_boundVars.isNonEmpty()) {
    TermList boundVar=_boundVars.pop();
    if(boundVar.isEmpty()) {
      return true;
    }
    _bindings.remove(boundVar);
  }
  return false;
}


bool SubstitutionTree::InstMatcher::matchNext(unsigned specVar, TermList nodeTerm, bool separate)
{
  CALL("SubstitutionTree::InstMatcher::matchNext");

  if(separate) {
    TermList sep;
    sep.makeEmpty();
    _boundVars.push(sep);
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


/**
 * @b nextSpecVar is the first unassigned special variable. Is being used
 * 	to determine size of array, that stores special variable bindings.
 * 	(To maximize performance, a DArray object is being used instead
 * 	of hash map.)
 * If @b reversed If true, parameters of supplied binary literal are
 * 	reversed. (useful for retrieval commutative terms)
 */
SubstitutionTree::FastInstancesIterator::FastInstancesIterator(SubstitutionTree* parent, Node* root,
	Term* query, bool retrieveSubstitution, bool reversed, bool withoutTop, bool useC, 
  FuncSubtermMap* fstm) //final two for compatibility purposes
: _literalRetrieval(query->isLiteral()), _retrieveSubstitution(retrieveSubstitution),
  _inLeaf(false), _ldIterator(LDIterator::getEmpty()),  _root(root),
  _alternatives(64), _specVarNumbers(64), _nodeTypes(64)
#if VDEBUG
  , _tree(parent)
#endif 
{
  CALL("SubstitutionTree::FastInstancesIterator::FastGeneralizationsIterator");
  ASS(root);
  ASS(!root->isLeaf());

#if VDEBUG
  _tree->_iteratorCnt++;
#endif

  Recycler::get(_subst);
  _subst->reset();
//  _subst=new InstMatcher;

  if(withoutTop){
    _subst->bindSpecialVar(0,TermList(query));
  }else{
    if(reversed) {
      createReversedInitialBindings(query);
    } else {
      createInitialBindings(query);
    }
  }
}

SubstitutionTree::FastInstancesIterator::~FastInstancesIterator()
{
#if VDEBUG
  _tree->_iteratorCnt--;
#endif
  Recycler::release(_subst);
//  delete _subst;
}


void SubstitutionTree::FastInstancesIterator::createInitialBindings(Term* t)
{
  CALL("SubstitutionTree::FastInstancesIterator::createInitialBindings");

  TermList* args=t->args();
  int nextVar = 0;
  while (! args->isEmpty()) {
    unsigned var = nextVar++;
    _subst->bindSpecialVar(var,*args);
    args = args->next();
  }
}

/**
 * For a binary comutative query literal, create the initial binding
 * where the order of special variables is reversed.
 */
void SubstitutionTree::FastInstancesIterator::createReversedInitialBindings(Term* t)
{
  CALL("SubstitutionTree::FastInstancesIterator::createReversedInitialBindings");
  ASS(t->isLiteral());
  ASS(t->commutative());
  ASS_EQ(t->arity(),2);

  _subst->bindSpecialVar(1,*t->nthArgument(0));
  _subst->bindSpecialVar(0,*t->nthArgument(1));
}

bool SubstitutionTree::FastInstancesIterator::hasNext()
{
  CALL("SubstitutionTree::FastInstancesIterator::hasNext");

  while(!_ldIterator.hasNext() && findNextLeaf()) {}
  return _ldIterator.hasNext();
}

#undef LOGGING
#define LOGGING 0

SubstitutionTree::QueryResult SubstitutionTree::FastInstancesIterator::next()
{
  CALL("SubstitutionTree::FastInstancesIterator::next");

  while(!_ldIterator.hasNext() && findNextLeaf()) {}
  ASS(_ldIterator.hasNext());
  LeafData& ld=_ldIterator.next();

  if(_retrieveSubstitution) {
    _resultDenormalizer.reset();
    bool ground=_literalRetrieval
	? ld.literal->ground()
	: (ld.term.isTerm() && ld.term.term()->ground());
    if(!ground) {
      Renaming normalizer;
      if(_literalRetrieval) {
	normalizer.normalizeVariables(ld.literal);
      } else {
	normalizer.normalizeVariables(ld.term);
      }
      _resultDenormalizer.makeInverse(normalizer);
    }

    return QueryResult(make_pair(&ld,
	    _subst->getSubstitution(&_resultDenormalizer)),UnificationConstraintStackSP());
  } else {
    return QueryResult(make_pair(&ld, ResultSubstitutionSP()),UnificationConstraintStackSP());
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
      curr=0;
      if(!sibilingsRemain && _alternatives.isNonEmpty()) {
	_subst->backtrack();
      }
      continue;
    }
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
      _subst->onLeafEntered(); //we reset the bindings cache
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
  ASSERT_VALID(*curr);
  ASS(!curr->isLeaf());

  IntermediateNode* inode=static_cast<IntermediateNode*>(curr);
  NodeAlgorithm currType=inode->algorithm();

  TermList query;
  InstMatcher::TermSpec querySpec;
  //here we are interested only in the top functor or the fact that the query is a variable
  //so we can discard the information about term origin
  if(_subst->findSpecVarBinding(inode->childVar, querySpec)) {
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
      _specVarNumbers.push(inode->childVar);
    }
    if(*nl && !noAlternatives) {
      _alternatives.push(nl);
      _nodeTypes.push(currType);
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
      ASS(query.isVar());
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
      return true;
    }
  }
  return false;
}


}
