/**
 * @file Clause.cpp
 * Implements class BDD for binary decision diagrams
 */

#include <utility>

#include "../Lib/Environment.hpp"
#include "../Lib/Exception.hpp"
#include "../Lib/DHMap.hpp"
#include "../Lib/Int.hpp"
#include "../Lib/List.hpp"
#include "../Lib/Stack.hpp"
#include "../Lib/Timer.hpp"
#include "../Lib/TimeCounter.hpp"

#include "../Kernel/Signature.hpp"

#include "../SAT/ClauseSharing.hpp"
#include "../SAT/Preprocess.hpp"
#include "../SAT/SATClause.hpp"
#include "../SAT/SATLiteral.hpp"
#include "../SAT/SingleWatchSAT.hpp"

#include "../Shell/Options.hpp"

#include "BDD.hpp"


namespace Kernel {

using namespace Lib;
using namespace SAT;

BDD* BDD::instance()
{
  CALL("BDD::instance");

  static BDD* inst=0;
  if(!inst) {
    inst=new BDD();
  }
  return inst;
}

BDD::BDD()
: _newVar(1)
{
  _trueNode._var=-1;
  _falseNode._var=-1;
#ifdef VDEBUG
  _trueNode._pos=0;
  _trueNode._neg=0;
  _falseNode._pos=0;
  _falseNode._neg=0;
#endif
}

BDD::~BDD()
{
  CALL("BDD::~BDD");

  NodeSet::Iterator nit(_nodes);
  while(nit.hasNext()) {
    BDDNode* node=nit.next();
    delete node;
  }
}

string BDD::getPropositionalPredicateName(int var)
{
  string prefix(BDD_PREDICATE_PREFIX);
  prefix+=env.options->namePrefix();
  string name = prefix + Int::toString(var);

  //We do not want the predicate to be already present!
  //(But we also don't want to insert it into signature,
  //as it would grow too much.)
  ASS(!env.signature->isPredicateName(name, 0));

  return name;
}

bool BDD::getNiceName(int var, string& res)
{
  return _niceNames.find(var, res);
}

BDDNode* BDD::getAtomic(int varNum, bool positive)
{
  CALL("BDD::getAtomic");
  ASS_GE(varNum,0);

  if(varNum>=_newVar) {
    _newVar=varNum+1;
  }

  if(positive) {
    return getNode(varNum, getTrue(), getFalse());
  } else {
    return getNode(varNum, getFalse(), getTrue());
  }
}

BDDNode* BDD::conjunction(BDDNode* n1, BDDNode* n2)
{
  CALL("BDD::conjunction");
  return getBinaryFnResult(n1,n2, ConjunctionFn(this));
}

BDDNode* BDD::disjunction(BDDNode* n1, BDDNode* n2)
{
  CALL("BDD::disjunction");
  return getBinaryFnResult(n1,n2, DisjunctionFn(this));
}

BDDNode* BDD::xOrNonY(BDDNode* x, BDDNode* y)
{
  CALL("BDD::xOrNonY");
  return getBinaryFnResult(x,y, XOrNonYFn(this));
}


bool BDD::isXOrNonYConstant(BDDNode* x, BDDNode* y, bool resValue)
{
  CALL("BDD::isXOrNonYConstant");
  return hasConstantResult(x,y, resValue, XOrNonYFn(this));
}

/**
 * Return pointer to BDDNode that represents result of applying
 * the binary function specified by the BinBoolFn functor to
 * @b n1 and @b n2. The binary functor BinBoolFn must allow to be
 * called as
 *
 * BDDNode* BinBoolFn(BDDNode* m1, BDDNode* m2)
 *
 * and return either result of applying the represented binary
 * function to @b m1 and @b m2, or 0 in case the result cannot
 * be determined by merely examining the objects pointed by
 * @b m1 and @b m2. It mustn't return 0 if both arguments are
 * either true or false BDD.
 */
template<class BinBoolFn>
BDDNode* BDD::getBinaryFnResult(BDDNode* n1, BDDNode* n2, BinBoolFn fn)
{
  CALL("BDD::getBinaryFnResult");
  ASS(n1);
  ASS(n2);

  TimeCounter tc(TC_BDD);

  int counter=0;

  static Stack<BDDNode*> toDo(8);
  //results stack contains zeroes and proper pointers standing for
  //intermediate results.
  //It can be viewed as a prefix of an expression in prefix notation
  //with 0 being a binary function and non-zeroes constants.
  //The expression is being simplified every time a well formed
  //subexpression (i.e. zero followed by two non-zeroes) appears.
  static Stack<BDDNode*> results(8);
  //Variable numbers to be used for building intermediate results in
  //the results stack.
  static Stack<int> vars(8);

  static DHMap<pair<BDDNode*,BDDNode*>, BDDNode*, PtrPairSimpleHash > cache;
  //if the cache was not reset, too much memory would be consumed
  cache.reset();

  for(;;) {
    counter++;
    if(counter==50000) {
      counter=0;
      if(env.timeLimitReached()) {
	throw TimeLimitExceededException();
      }
    }
    BDDNode* res=fn(n1,n2);
    if(res || cache.find(make_pair(n1, n2), res)) {
      while(results.isNonEmpty() && results.top()!=0) {
	BDDNode* pos=results.pop();
	BDDNode* neg=res;
	unsigned var=vars.pop();
	if(pos==neg) {
	  res=pos;
	} else {
	  res=getNode(var, pos, neg);
	}
	ASS_EQ(results.top(),0);
	results.pop();
	BDDNode* arg1=results.pop();
	BDDNode* arg2=results.pop();
	if( !(counter%4) ) {
	  cache.insert(make_pair(arg1, arg2), res);
	}
      }
      results.push(res);
    } else {
      //we split at variables with higher numbers first
      int splitVar=max(n1->_var, n2->_var);
      ASS_GE(splitVar,0);
      toDo.push((n2->_var==splitVar) ? n2->_neg : n2);
      toDo.push((n1->_var==splitVar) ? n1->_neg : n1);
      toDo.push((n2->_var==splitVar) ? n2->_pos : n2);
      toDo.push((n1->_var==splitVar) ? n1->_pos : n1);
      results.push(n2);
      results.push(n1);
      results.push(0);
      //now push arguments at the stack, so that we know store the
      //answer into the cache
      vars.push(splitVar);
    }

    if(toDo.isEmpty()) {
      break;
    }
    n1=toDo.pop();
    n2=toDo.pop();
  }

  ASS(toDo.isEmpty());
  ASS_EQ(results.length(),1);
  return results.pop();
}

/**
 * Return true iff the result of applying the binary function specified
 * by the BinBoolFn functor to @b n1 and @b n2 is a constant BDD with truth
 * value equal to @b resValue.
 *
 * The binary functor BinBoolFn must allow to be called as
 *
 * BDDNode* BinBoolFn(BDDNode* m1, BDDNode* m2)
 *
 * and return either result of applying the represented binary
 * function to @b m1 and @b m2, or 0 in case the result cannot
 * be determined by merely examining the objects pointed by
 * @b m1 and @b m2. It mustn't return 0 if both arguments are
 * either true or false BDD.
 */
template<class BinBoolFn>
bool BDD::hasConstantResult(BDDNode* n1, BDDNode* n2, bool resValue, BinBoolFn fn)
{
  CALL("BDD::hasConstantResult");
  ASS(n1);
  ASS(n2);

  TimeCounter tc(TC_BDD);

  int counter=0;

  static Stack<BDDNode*> toDo(8);
  toDo.reset();

  static DHMap<pair<BDDNode*,BDDNode*>, bool, PtrPairSimpleHash > cache;
  cache.reset();

  for(;;) {
    counter++;
    if(counter==50000) {
      counter=0;
      if(env.timeLimitReached()) {
	throw TimeLimitExceededException();
      }
    }
    BDDNode* res=fn(n1,n2);
    if(res) {
      if( (resValue && !isTrue(res)) ||
	      (!resValue && !isFalse(res))) {
	return false;
      }
    } else {
      if(!cache.find(make_pair(n1, n2)))
      {
	//we split at variables with higher numbers first
	int splitVar=max(n1->_var, n2->_var);
	ASS_GE(splitVar,0);
	toDo.push((n2->_var==splitVar) ? n2->_neg : n2);
	toDo.push((n1->_var==splitVar) ? n1->_neg : n1);
	toDo.push((n2->_var==splitVar) ? n2->_pos : n2);
	toDo.push((n1->_var==splitVar) ? n1->_pos : n1);

	if( !(counter%4) ) {
	  cache.insert(make_pair(n1, n2), false);
	}
      }
    }

    if(toDo.isEmpty()) {
      break;
    }
    n1=toDo.pop();
    n2=toDo.pop();
  }

  return true;
}


BDDNode* BDD::ConjunctionFn::operator()(BDDNode* n1, BDDNode* n2)
{
  if(_parent->isFalse(n1) || _parent->isFalse(n2)) {
    return _parent->getFalse();
  }
  if(_parent->isTrue(n1)) {
    return n2;
  }
  if(_parent->isTrue(n2)) {
    return n1;
  }
  return 0;
}

BDDNode* BDD::DisjunctionFn::operator()(BDDNode* n1, BDDNode* n2)
{
  if(_parent->isTrue(n1) || _parent->isTrue(n2)) {
    return _parent->getTrue();
  }
  if(_parent->isFalse(n1)) {
    return n2;
  }
  if(_parent->isFalse(n2)) {
    return n1;
  }
  return 0;
}

BDDNode* BDD::XOrNonYFn::operator()(BDDNode* n1, BDDNode* n2)
{
  if(_parent->isTrue(n1) || _parent->isFalse(n2)) {
    return _parent->getTrue();
  }
  if(_parent->isTrue(n2)) {
    return n1;
  }
  return 0;
}


BDDNode* BDD::getNode(int varNum, BDDNode* pos, BDDNode* neg)
{
  CALL("BDD::getNode");
  ASS_GE(varNum,0);
  ASS_L(varNum,_newVar);
  ASS_NEQ(pos,neg);

  //newNode contains either 0 or pointer to a BDDNode that
  //hasn't been used yet.
  static BDDNode* newNode=0;

  if(newNode==0) {
    newNode=new BDDNode();
  }

  newNode->_var=varNum;
  newNode->_pos=pos;
  newNode->_neg=neg;

  BDDNode* res=_nodes.insert(newNode);
  if(res==newNode) {
    newNode=0;
  }
  return res;
}


string BDD::toString(BDDNode* node)
{
  string res="";
  static Stack<BDDNode*> nodes(8);
  nodes.push(node);
  while(nodes.isNonEmpty()) {
    BDDNode* n=nodes.pop();
    bool canPrintSeparator=true;
    if(n==0) {
      res+=") ";
    } else if(isTrue(n)) {
      res+="$true ";
    } else if(isFalse(n)) {
      res+="$false ";
    } else {
      res+=string("( ")+Int::toString(n->_var)+" ? ";
      nodes.push(0);
      nodes.push(n->_neg);
      nodes.push(n->_pos);
      canPrintSeparator=false;
    }
    if(canPrintSeparator && nodes.isNonEmpty() && nodes.top()) {
      res+=": ";
    }
  }
  return res;
}

string BDD::toTPTPString(BDDNode* node, string bddPrefix)
{
  if(isTrue(node)) {
    return "$true";
  } else if(isFalse(node)) {
    return "$false";
  } else {
    return string("( ( ")+bddPrefix+Int::toString(node->_var)+" => "+toTPTPString(node->_pos, bddPrefix)+
      ") & ( ~"+bddPrefix+Int::toString(node->_var)+" => "+toTPTPString(node->_neg, bddPrefix)+" ) )";
  }
}

string BDD::toTPTPString(BDDNode* node)
{
  if(isTrue(node)) {
    return "$true";
  } else if(isFalse(node)) {
    return "$false";
  } else {
    return string("( ( ")+getPropositionalPredicateName(node->_var)+" => "+toTPTPString(node->_pos)+
      ") & ( ~"+getPropositionalPredicateName(node->_var)+" => "+toTPTPString(node->_neg)+" ) )";
  }
}


bool BDD::equals(const BDDNode* n1,const BDDNode* n2)
{
  return n1->_var==n2->_var && n1->_pos==n2->_pos && n1->_neg==n2->_neg;
}
unsigned BDD::hash(const BDDNode* n)
{
  CALL("BDD::hash");

  unsigned res=Hash::hash(n->_var);
  res=Hash::hash(n->_pos, res);
  res=Hash::hash(n->_neg, res);
  return res;
}

/**
 * Convert a BDD node into a sequence of propositional clauses.
 */
SATClauseList* BDD::toCNF(BDDNode* node)
{
  CALL("BDD::toCNF");

  SATClauseList* res=0;
  static Stack<pair<BDDNode*,bool> > stack;
  stack.reset();

  for(;;) {
    while(!isConstant(node)) {
      stack.push(make_pair(node, false));
      node=node->_neg;
    }
    if(isFalse(node)) {
      unsigned clen=stack.size();
      SATClause* cl=new(clen) SATClause(clen, true);

      for(unsigned i=0;i<clen;i++) {
	(*cl)[i]=SATLiteral(stack[i].first->_var, !stack[i].second);
      }

      SATClauseList::push(cl, res);
    }
    while(stack.isNonEmpty() && stack.top().second==true) {
      stack.pop();
    }
    if(stack.isEmpty()) {
      return res;
    }
    ASS(!stack.top().second);
    stack.top().second=true;
    node=stack.top().first->_pos;
  }
}


void BDDConjunction::addNode(BDDNode* n)
{
  CALL("BDDConjunction::addNode");

  if(_isFalse) {
    return;
  }
  if(_bdd->isConstant(n)) {
    if(_bdd->isFalse(n)) {
      _isFalse=true;
    } else {
      ASS(_bdd->isTrue(n));
    }
    return;
  }

  TimeCounter tc(TC_SAT_SOLVER);

  if(n->_var > _maxVar) {
    _maxVar=n->_var;
  }


  unsigned varCnt=_maxVar+1;

  SATClauseList* newClLst=_bdd->toCNF(n);
#if 1
  _solver.ensureVarCnt(varCnt);
  _solver.addClauses(pvi( SATClauseList::DestructiveIterator(newClLst) ));

  if(_solver.getStatus()==TWLSolver::UNSATISFIABLE) {
    _isFalse=true;
  }

#else
  SATClauseList* oldClLst=_clauses;

//  cout<<"\n\n----------------------------------\n";
//  {
//    SATClauseIterator cit=pvi( getConcatenatedIterator(
//	    SATClauseList::Iterator(oldClLst),
//	    SATClauseList::Iterator(newClLst)) );
//    while(cit.hasNext()) {
//      cout<<(*cit.next())<<endl;
//    }
//    cout<<"---Unit propagation---\n";
//  }

//  SATClauseIterator allClIt=pvi( getConcatenatedIterator(
//	  SATClauseList::DestructiveIterator(oldClLst),
//	  SATClauseList::DestructiveIterator(newClLst)) );
//  SATClauseIterator cit=Preprocess::propagateUnits(varCnt,
//	  Preprocess::removeDuplicateLiterals(allClIt));

  SATClauseIterator inpClauses=pvi( getConcatenatedIterator(
	  getConcatenatedIterator(SATClauseList::DestructiveIterator(_units),
		  SATClauseList::DestructiveIterator(_clauses) ),
	  SATClauseList::DestructiveIterator(newClLst)) );

  SATClauseIterator newUnitIt;
  SATClauseIterator newClauseIt;
  Preprocess::propagateUnits(inpClauses, newUnitIt, newClauseIt);

  ClauseSharing sharing;

  _clauses=0;
  while(newClauseIt.hasNext()) {
    SATClause* cl=newClauseIt.next();
    if(sharing.insert(cl)==cl) {
//      cout<<(*cl)<<endl;
      SATClauseList::push(cl,_clauses);
    }
  }

  _units=0;
  while(newUnitIt.hasNext()) {
    SATClause* cl=newUnitIt.next();
//    cout<<"U: "<<(*cl)<<endl;
    SATClauseList::push(cl,_units);
  }

//  cout<<"---------\n";

//  SATClauseIterator solverClauses=Preprocess::filterPureLiterals(varCnt, pvi( getContentIterator(_clauses) ));
  SATClauseIterator solverClauses=pvi( getContentIterator(_clauses) );

#if 1
  TWLSolver alg;
  alg.ensureVarCnt(varCnt);
  alg.addClauses(solverClauses);

  if(alg.getStatus()==TWLSolver::UNSATISFIABLE) {
    _isFalse=true;
  }
#else
  SingleWatchSAT alg(varCnt);
  bool proceed=alg.loadClauses(solverClauses);
  if(proceed) {
    alg.satisfy(env.remainingTime());
  }

  if(alg.termination==SingleWatchSAT::TIME_LIMIT) {
    throw TimeLimitExceededException();
  } else if(alg.termination==SingleWatchSAT::REFUTATION) {
    _isFalse=true;
  }
#endif

#endif

//  cout<<"add node finished "<<_isFalse<<endl;
  return;
}


}
