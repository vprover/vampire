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

BDDClausifier::BDDClausifier(bool naming)
: _nextCNFVar(1), _maxBDDVar(1)
{
  _naming=naming;
  _useSR=env.options->satSolverWithSubsumptionResolution();
}

void BDDClausifier::clausify(BDDNode* node, SATClauseStack& acc)
{
  CALL("BDDClausifier::clausify");

  if(_useSR) {
    clausifyWithSR(node, acc);
  }
  else {
    clausifyWithoutSR(node, acc);
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


struct BDDClausifier::CNFStackRec {
  CNFStackRec(BDDNode* n, bool firstPos, bool second=false) : n(n), firstPos(firstPos),
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

void BDDClausifier::clausifyWithSR(BDDNode* node, SATClauseStack& acc)
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
      //the new SATClause will contain literal for each non-resolved stack item
      unsigned clen=stack.size()-resolvedCnt;
      SATClause* cl=new(clen) SATClause(clen, true);

      unsigned si=stack.size();
      for(unsigned ci=0;ci<clen;ci++) {
	do {
	  si--;
	  ASS_GE(si,0);
	} while(stack[si].resolved);
	CNFStackRec& sr=stack[si];
	(*cl)[ci]=SATLiteral(getCNFVar(sr.n->_var), !(sr.second^sr.firstPos));
      }

      acc.push(cl);

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

void BDDClausifier::clausifyWithoutSR(BDDNode* node, SATClauseStack& acc)
{
  CALL("BDDClausifier::clausifyWithoutSR");

  BDD* bdd=BDD::instance();

  static Stack<pair<BDDNode*,bool> > stack;
  stack.reset();

  for(;;) {
    while(!bdd->isConstant(node)) {
      stack.push(make_pair(node, false));
      node=node->_neg;
    }
    if(bdd->isFalse(node)) {
      unsigned clen=stack.size();
      SATClause* cl=new(clen) SATClause(clen, true);

      for(unsigned i=0;i<clen;i++) {
        (*cl)[i]=SATLiteral(getCNFVar(stack[i].first->_var), !stack[i].second);
      }

      acc.push(cl);
    }
    while(stack.isNonEmpty() && stack.top().second==true) {
      stack.pop();
    }
    if(stack.isEmpty()) {
      return;
    }
    ASS(!stack.top().second);
    stack.top().second=true;
    node=stack.top().first->_pos;
  }
}


}
