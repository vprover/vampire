/**
 * @file BDDClausifier.cpp
 * Implements class BDDClausifier.
 */

#include "Lib/BinaryHeap.hpp"
#include "Lib/Int.hpp"
#include "Lib/MapToLIFO.hpp"

#include "SAT/SATClause.hpp"
#include "SAT/SATLiteral.hpp"

#include "BDD.hpp"

#include "BDDClausifier.hpp"

#undef LOGGING
#define LOGGING 0

namespace Kernel
{

using namespace Lib;
using namespace SAT;

/**
 * Struct used by a stack in DFS traversal of BDDs during clausification
 */
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

BDDClausifier::BDDClausifier(bool subsumptionResolution, bool naming)
: _nextCNFVar(1), _maxBDDVar(1)
{
  _naming=naming;
  _useSR=subsumptionResolution;
}

/**
 * Clausify @b node and add resulting clauses into @b acc.
 *
 * Based on the value of the member variable @b _useSR,
 * the subsumption resolution is either used or not.
 *
 * If the member variable @b _naming is set to true,
 * the function @b introduceNames() is called before
 * the actual clausification to introduce names that may
 * reduce the number of generated clauses.
 */
void BDDClausifier::clausify(BDDNode* node, SATClauseStack& acc)
{
  if(_naming) {
    introduceNames(node, acc);
  }
  clausify(node, acc, 0);
}


/**
 * Clausify @b node and add resulting clauses into @b acc. If
 * @b givenName is non-zero, add negative occurrence of the
 * @b givenName CNF variable into each generated clause
 * (this is used to generate name definition clauses).
 *
 * Based on the value of the member variable @b _useSR,
 * the subsumption resolution is either used or not.
 */
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

/**
 * Return the number of used CNF variables
 *
 * The used CNF variables are then {1,...,(returned value)-1}
 */
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

  if(!_naming) {
    return 0;
  }
  return _names.get(node, 0);
}

/**
 * Assign name to BDD node @b node, add name defining clauses to @b acc
 * and return the assigned name
 */
unsigned BDDClausifier::assignName(BDDNode* node, SATClauseStack& acc)
{
  CALL("BDDClausifier::assignName");
  ASS(_naming);
  ASS_EQ(getName(node), 0); //not already named

  unsigned name=_nextCNFVar++;
  clausify(node, acc, name);
  ALWAYS(_names.insert(node, name));
  LOG("name "<<name<<" assigned to node "<<BDD::instance()->toString(node));
  return name;
}

/**
 * Return number of CNF variable that corresponds to the BDD variable @b bddVar
 *
 * If naming is disabled, this function is an identity.
 */
unsigned BDDClausifier::getCNFVar(unsigned bddVar)
{
  CALL("BDDClausifier::getSatVar");

  if(bddVar>_maxBDDVar) {
    _maxBDDVar=bddVar;
  }

  if(!_naming) {
    return bddVar;
  }

  unsigned cnfVar;
  if(_bdd2cnfVars.findOrInsert(bddVar, cnfVar, _nextCNFVar)) {
    LOG("bdd var "<<bddVar<<" has assigned cnf var "<<cnfVar);
    _nextCNFVar++;
  }
  return cnfVar;
}

/**
 * Return pointer to new SATClause object containing literals
 * corresponding to non-resolved entries in @b stack (the number of
 * resolved entried is passed in @b resolvedCnt to spare one pass
 * through the stack). If @b givenName is non-zero, negative occurrence
 * of the CNF variable @b givenName is added to the clause. If
 * @b nodeName is non-zero, positive occurrence of the CNF variable
 * @b nodeName is added to the clause.
 *
 * Specifying @b givenName is used to build a name definition clause,
 * and specifying @b nodeName is used to refer to a name of a node.
 */
SATClause* BDDClausifier::buildClause(unsigned givenName, Stack<CNFStackRec>& stack, unsigned resolvedCnt,
    unsigned nodeName)
{
  CALL("BDDClausifier::buildClause");
  ASS_REP2(!givenName || givenName>nodeName,givenName,nodeName); //the newly given name must be greater than previously given ones

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

/**
 * Clausify @b node0 and add resulting clauses into @b acc. Try
 * to simplify generated clauses by each other using subsumption
 * resolution. If @b givenName is non-zero, add negative occurrence
 * of the @b givenName CNF variable into each generated clause
 * (this is used to generate name definition clauses).
 */
void BDDClausifier::clausifyWithSR(BDDNode* node, SATClauseStack& acc, unsigned givenName)
{
  CALL("BDDClausifier::clausifyWithSR");

  BDD* bdd=BDD::instance();

  int resolvedCnt=0; //number of resolved literals on the stack
  static Stack<CNFStackRec> stack;
  stack.reset();

  for(;;) {
    if(!bdd->isConstant(node)) {

      unsigned name=getName(node);
      if(name) {
        acc.push(buildClause(givenName, stack, resolvedCnt, name));
	goto node_handled;
      }

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
      continue;
    }
    if(bdd->isFalse(node)) {
      acc.push(buildClause(givenName, stack, resolvedCnt));

      if(!stack.top().second) {
	stack.top().resolved=true;
	resolvedCnt++;
      }
    }

  node_handled:
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

/**
 * Clausify @b node0 and add resulting clauses into @b acc. If
 * @b givenName is non-zero, add negative occurrence of the
 * @b givenName CNF variable into each generated clause
 * (this is used to generate name definition clauses).
 */
void BDDClausifier::clausifyWithoutSR(BDDNode* node0, SATClauseStack& acc, unsigned givenName)
{
  CALL("BDDClausifier::clausifyWithoutSR");

  BDD* bdd=BDD::instance();

  BDDNode* node=node0;

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

/**
 * Introduce names for some nodes used by @b node0 in order to reduce
 * amount of clauses generated during its clausification. Add name
 * defining clauses into @b acc.
 */
void BDDClausifier::introduceNames(BDDNode* node0, SATClauseStack& acc)
{
  CALL("BDDClausifier::introduceNames");

  BDD* bdd=BDD::instance();

  if(bdd->isConstant(node0) || getName(node0)) {
    return;
  }

  static BinaryHeap<unsigned, ReversedComparator<Int> > varNums;
  static DHMap<BDDNode*, unsigned> occurrenceCounts;
  static MapToLIFO<unsigned, BDDNode*> nodesToExamine;
  static Stack<BDDNode*> nodesToName;

  varNums.reset();
  occurrenceCounts.reset();
  nodesToExamine.reset();
  nodesToName.reset();


  varNums.insert(node0->_var);
  nodesToExamine.pushToKey(node0->_var, node0);

  while(!varNums.isEmpty()) {
    unsigned var=varNums.pop();
    ASS(varNums.isEmpty() || varNums.top()<var);

    while(!nodesToExamine.isKeyEmpty(var)) {
      BDDNode* node=nodesToExamine.popFromKey(var);
      ASS_EQ(node->_var, var);
      ASS(!bdd->isConstant(node));
      ASS(!getName(node));

      unsigned occurrences;
      if(occurrenceCounts.find(node,occurrences) && occurrences>=2) {
	nodesToName.push(node);
      }

      for(int i=0;i<2;i++) {
	BDDNode* childNode= i ? node->_neg : node->_pos;

	if(bdd->isConstant(childNode) || getName(childNode)) {
	  continue;
	}
	//If node has one child equal to true, it won't be named, as it
	//does not add an extra CNF clause. Also we name only ondes with
	//even variable numbers to decrease number of names.
	bool nameable=!bdd->isTrue(childNode->_pos) && !bdd->isTrue(childNode->_neg) &&
	    childNode->_var%2==0;
	bool shouldBeExamined=true;
	if(nameable) {
	  unsigned* ocPtr;
	  if(!occurrenceCounts.getValuePtr(childNode, ocPtr, 0)) {
	    //this node is already marked for examination and there
	    //is no need to examine it multiple times, as it is nameable
	    shouldBeExamined=false;
	  }
	  (*ocPtr)++;
	}
	if(shouldBeExamined) {
	  unsigned chVar=childNode->_var;
	  if(nodesToExamine.isKeyEmpty(chVar)) {
	    varNums.insert(chVar);
	  }
	  nodesToExamine.pushToKey(chVar, childNode);
	}
      }
    }
  }

  while(nodesToName.isNonEmpty()) {
    BDDNode* node=nodesToName.pop();
    //It is important that here we will first introduce names for nodes
    //with low BDD variables. This way we will be able to use these
    //names when naming nodes with higher variables.
    ASS(nodesToName.isEmpty() || nodesToName.top()->_var >= node->_var);
    assignName(node, acc);
  }
}

}















