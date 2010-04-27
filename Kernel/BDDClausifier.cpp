/**
 * @file BDDClausifier.cpp
 * Implements class BDDClausifier.
 */

#include "../Lib/Environment.hpp"

#include "../SAT/SATClause.hpp"
#include "../SAT/SATLiteral.hpp"

#include "../Shell/Options.hpp"

#include "BDD.hpp"

#include "BDDClausifier.hpp"

namespace Kernel
{

using namespace Lib;
using namespace SAT;

struct BDDClausifier::CNFStackRec {
  CNFStackRec(BDDNode* n, bool firstPos=false, bool second=false) : n(n), firstPos(firstPos),
  second(second), resolved(false) {}

  BDDNode* n;
  /** we first descended into node's @b _pos child */
  bool firstPos;
  /** we are already in the second child of the node */
  bool second;
  /** true if the literal is resolved and therefore  it should not be put into created clauses
   *
   * Loop invariant: can be true only if @b second is true */
  bool resolved;
};

BDDClausifier::BDDClausifier(bool naming)
: _nextCNFVar(1), _maxBDDVar(1)
{
  _naming=naming;
  _useSR=env.options->satSolverWithSubsumptionResolution();
}

void BDDClausifier::clausify(BDDNode* node, SATClauseStack& acc, unsigned givenName)
{
  CALL("BDDClausifier::clausify");

  if(_useSR) {
    clausifyWithSR(node, acc, givenName);
  }
  else {
    clausifyWithoutSR(node, acc, givenName);
  }
}

unsigned BDDClausifier::getCNFVarCount()
{
  CALL("BDDClausifier::getCNFVarCount");

  if(_naming) {
    return _nextCNFVar;
  }
  else {
    return _maxBDDVar+1;
  }
}

/**
 * Return either name of @b node or 0 if @b node is not named
 */
unsigned BDDClausifier::getName(BDDNode* node)
{
  CALL("BDDClausifier::getName");

  return _names.get(node, 0);
}

unsigned BDDClausifier::name(BDDNode* node, SATClauseStack& acc)
{
  CALL("BDDClausifier::name");

  NOT_IMPLEMENTED;
}

unsigned BDDClausifier::getCNFVar(unsigned bddVar)
{
  CALL("BDDClausifier::getSatVar");

  if(bddVar>_maxBDDVar) {
    _maxBDDVar=bddVar;
  }

  if(!_naming) {
    return bddVar;
  }

  unsigned sv;
  if(_bdd2cnfVars.findOrInsert(bddVar, sv, _nextCNFVar)) {
    _nextCNFVar++;
  }
  return sv;
}

SATClause* BDDClausifier::buildClause(unsigned givenName, Stack<CNFStackRec>& stack, unsigned resolvedCnt,
    unsigned nodeName)
{
  CALL("BDDClausifier::buildClause");
  ASS(!givenName || givenName>nodeName); //the newly given name must be greater than previously given ones

  //the new SATClause will contain literal for each non-resolved stack item
  //and possibly for the name of the inner node and the naming literal of node
  //that is being named
  unsigned nonNameLen=stack.size()-resolvedCnt;
  unsigned clen=nonNameLen+(nodeName?1:0)+(givenName?1:0);
  SATClause* cl=new(clen) SATClause(clen, true);

  unsigned si=stack.size();
  for(unsigned ci=0;ci<nonNameLen;ci++) {
    do {
      si--;
      ASS_GE(si,0);
    } while(stack[si].resolved);
    CNFStackRec& sr=stack[si];
    (*cl)[ci]=SATLiteral(getCNFVar(sr.n->_var), !(sr.second^sr.firstPos));
  }

  if(nodeName) {
    (*cl)[nonNameLen]=SATLiteral(nodeName, true);
  }
  if(givenName) {
    (*cl)[clen-1]=SATLiteral(givenName, false);
  }

  return cl;
}

void BDDClausifier::clausifyWithSR(BDDNode* node, SATClauseStack& acc, unsigned givenName)
{
  CALL("BDDClausifier::clausifyWithSR");

  BDD* bdd=BDD::instance();

  int resolvedCnt=0; //number of resolved literals on the stack
  static Stack<CNFStackRec> stack;
  stack.reset();

  for(;;) {
    while(!bdd->isConstant(node)) {
      if(bdd->isTrue(node->_pos)) {
	stack.push(CNFStackRec(node, true, true));
	node=node->_neg;
      }
      else if(bdd->isTrue(node->_neg)) {
	stack.push(CNFStackRec(node, false, true));
	node=node->_pos;
      }
      else if(bdd->isFalse(node->_pos)) {
	stack.push(CNFStackRec(node, true));
	node=node->_pos;
      }
      else {
	stack.push(CNFStackRec(node, false));
	node=node->_neg;
      }
    }
    if(bdd->isFalse(node)) {
      acc.push(buildClause(givenName, stack, resolvedCnt));

      if(!stack.top().second) {
	stack.top().resolved=true;
	resolvedCnt++;
      }
    }
    while(stack.isNonEmpty() && stack.top().second) {
      if(stack.top().resolved) {
	resolvedCnt--;
      }
      stack.pop();
    }
    if(stack.isEmpty()) {
      return;
    }

    CNFStackRec& sr=stack.top();
    ASS(!sr.second);
    //move to the other child
    sr.second=true;
    if(sr.firstPos) {
      node=sr.n->_neg;
    }
    else {
      node=sr.n->_pos;
    }
  }
}

void BDDClausifier::clausifyWithoutSR(BDDNode* node, SATClauseStack& acc, unsigned givenName)
{
  CALL("BDDClausifier::clausifyWithoutSR");

  BDD* bdd=BDD::instance();

  static Stack<CNFStackRec> stack;
  stack.reset();

  for(;;) {
    if(!bdd->isConstant(node)) {

      unsigned name=getName(node);
      if(name) {
        acc.push(buildClause(givenName, stack, 0, name));
	goto node_handled;
      }

      stack.push(CNFStackRec(node));
      node=node->_neg;
      continue;
    }
    else {
      if(bdd->isFalse(node)) {
        acc.push(buildClause(givenName, stack));
      }
    }
  node_handled:
    while(stack.isNonEmpty() && stack.top().second==true) {
      stack.pop();
    }
    if(stack.isEmpty()) {
      return;
    }
    ASS(!stack.top().second);
    stack.top().second=true;
    node=stack.top().n->_pos;
  }
}


}
