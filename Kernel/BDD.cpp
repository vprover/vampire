/**
 * @file Clause.cpp
 * Implements class BDD for binary decision diagrams
 */

#include "../Lib/Stack.hpp"

#include "BDD.hpp"

namespace Kernel {

using namespace Lib;

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
: _newVar(0)
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

/**
 * Return pointer to BDDNode that represents result of applying
 * the binary function specified by the BinBoolFn functor to
 * @b n1 and @n2. The binary functor BinBoolFn must allow to be
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

  for(;;) {
    BDDNode* res=fn(n1,n2);
    if(res) {
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
      results.push(0);
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


}
