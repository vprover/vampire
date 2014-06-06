/**
 * @file AIG.cpp
 * Implements class AIG.
 */

#include <algorithm>
#include <sstream>

#include "Lib/Allocator.hpp"
#include "Lib/MapToLIFO.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/SCCAnalyzer.hpp"
#include "Lib/ScopedPtr.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/ColorHelper.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/FormulaVarIterator.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"

#include "Shell/Options.hpp"

#include "PDUtils.hpp"
#include "SimplifyFalseTrue.hpp"

#include "AIG.hpp"

namespace Shell
{

using namespace Kernel;

class AIG::Node {
public:
  enum Kind {
    ATOM,
    TRUE_CONST,
    CONJ,
    /** Universal quantifier */
    QUANT
  };

  CLASS_NAME(AIG::Node);
  USE_ALLOCATOR(Node);
private:
  Kind _kind;
  unsigned _nodeIdx;
  union {
    /**
     * Valid if _kind==ATOM
     *
     * Must be positive.
     */
    Literal* _lit;

    /**
     * Valid if _kind==CONJ
     *
     * Parent nodes of the AIG node
     */
    RefProxy _pars[2];

    /** Valid if _kind==QUANT */
    struct {
      RefProxy _qPar;
      VarSet* _qVars;
    };
  };
  /**
   * We make use of the fact that pointers are 4 byte aligned,
   * so we may use the first two bits of the _freeVars set to
   * store color of the AIG.
   */
  union {
    /** to obtain pointer to the VarSet freeVars, the two least
     * significant bits must be set to 0 */
    size_t _freeVars;
    unsigned _color : 2;
  };

public:
  Node(Kind k) : _kind(k) {
    ASS_NEQ(k,ATOM);
    if(k==QUANT) {
      _qVars = 0;
    }
  }
  Node(Literal* atm) : _kind(ATOM), _lit(atm) { ASS(atm->isPositive()); }

  ~Node() {
  }

  Kind kind() const { return _kind; }
  /**
   * Index of the node which is unique among nodes with
   * the same parent AIG object.
   *
   * We assign indexes to nodes so we can deterministically normalize
   * node order in conjunction nodes. Also an invariant holds that parent
   * nodes always have lower index than their child.
   */
  unsigned nodeIdx() const { return _nodeIdx; }

  /**
   * Should be called only during node creation
   */
  void setNodeIdx(unsigned idx) { _nodeIdx = idx; }


  Literal* literal() const
  {
    CALL("AIG::Node::literal");
    ASS_EQ(kind(), ATOM);
    return _lit;
  }
  Ref parent(unsigned i) const {
    CALL("AIG::Node::parent");
    ASS_EQ(kind(), CONJ);
    return _pars[i];
  }

  Ref qParent() const {
    CALL("AIG::Node::qParent");
    ASS_EQ(kind(), QUANT);
    return _qPar;
  }
  VarSet* qVars() const {
    CALL("AIG::Node::qVars");
    ASS_EQ(kind(), QUANT);
    return _qVars;
  }

  void setConjParents(Ref par1,Ref par2)
  {
    ASS_EQ(kind(), CONJ);
    _pars[0] = par1;
    _pars[1] = par2;
  }
  void setQuantArgs(VarSet* vars, Ref par)
  {
    ASS_EQ(kind(), QUANT);
    _qVars = vars;
    _qPar = par;
  }

  VarSet* getFreeVars() const {
    return reinterpret_cast<VarSet*>(_freeVars & ~ static_cast<size_t>(3));
  }

  Color getColor() const {
    return static_cast<Color>(_color);
  }

  /** Can be called after parents are set for nodes that have parents */
  void setPrecomputedValues()
  {
    CALL("AIG::Node::setFreeVars");

    Color clr;
    VarSet* vars;
    switch(_kind) {
    case TRUE_CONST:
      vars = VarSet::getEmpty();
      clr = COLOR_TRANSPARENT;
      break;
    case ATOM:
      vars = getTermFreeVars(literal());
      clr = literal()->color();
      break;
    case CONJ:
      vars = parent(0).getFreeVars()->getUnion(parent(1).getFreeVars());
      clr = ColorHelper::combine(parent(0).getColor(), parent(1).getColor());
      break;
    case QUANT:
      vars = qParent().getFreeVars()->subtract(qVars());
      clr = qParent().getColor();
      break;
    }
    ASS_EQ(reinterpret_cast<size_t>(vars)&3, 0);
    _freeVars = reinterpret_cast<size_t>(vars) | clr;
  }
};

/**
 * Can be used for both terms and literals
 */
AIG::VarSet* AIG::getTermFreeVars(Term* trm)
{
  CALL("AIG::getTermFreeVars");

  if(trm->shared()) {
    if(trm->ground()) {
      return VarSet::getEmpty();
    }
    VariableIterator vit;
    vit.reset(trm);
    return VarSet::getFromIterator(getMappingIterator<VariableIterator&>(vit, OrdVarNumberExtractorFn()));
  }

  FormulaVarIterator fvit(trm);
  return VarSet::getFromIterator(fvit);
}

unsigned AIG::NodeHash::hash(Node* n)
{
  CALL("AIG::NodeHash::hash");
  switch(n->kind()) {
  case Node::TRUE_CONST:
    return 1;
  case Node::ATOM:
    return 2+PtrIdentityHash::hash(n->literal());
  case Node::CONJ:
  {
    unsigned p1 = n->parent(0).hash();
    unsigned p2 = n->parent(1).hash();
    return HashUtils::combine(3, HashUtils::combine(p1, p2));
  }
  case Node::QUANT:
  {
    unsigned res = n->qParent().hash();
    VarSet::Iterator vit(*n->qVars());
    while(vit.hasNext()) {
      res = HashUtils::combine(res, vit.next());
    }
    return res;
  }
  default:
    ASSERTION_VIOLATION;
  }
}

bool AIG::NodeHash::equals(Node* n1, Node* n2)
{
  CALL("AIG::NodeHash::equals");

  if(n1->kind()!=n2->kind()) { return false; }
  switch(n1->kind()) {
  case Node::TRUE_CONST:
    return true;
  case Node::ATOM:
    return n1->literal()==n2->literal();
  case Node::CONJ:
    //nodes cannot be equal after swapping of parents, because we normalize their order
    ASS(n1->parent(0)!=n2->parent(1) || n1->parent(1)!=n2->parent(0));
    return n1->parent(0)==n2->parent(0) && n1->parent(1)==n2->parent(1);
  case Node::QUANT:
    return n1->qParent()==n2->qParent() && n1->qVars()==n2->qVars();
  default:
    ASSERTION_VIOLATION;
  }
}


bool AIG::Ref::isPropConst() const
{
  return node()->kind()==Node::TRUE_CONST;
}

bool AIG::Ref::isAtom() const
{
  return node()->kind()==Node::ATOM;
}

bool AIG::Ref::isQuantifier() const
{
  return node()->kind()==Node::QUANT;
}

bool AIG::Ref::isConjunction() const
{
  return node()->kind()==Node::CONJ;
}

/**
 * Return literal of the positive form of the current AIG.
 * (The returned literal is always with positive polarity.)
 *
 * The current AIG must be an atom (isAtom() returns true).
 */
Literal* AIG::Ref::getPositiveAtom() const
{
  CALL("AIG::Ref::getPositiveAtom");
  ASS(isAtom());
  ASS(node()->literal()->isPositive());
  return node()->literal();
}

/**
 * Return variables of a quantifier node
 */
AIG::VarSet* AIG::Ref::getQuantifierVars() const
{
  CALL("AIG::Ref::getQuantifierVars");
  ASS(isQuantifier());
  return node()->qVars();
}

AIG::VarSet* AIG::Ref::getFreeVars() const
{
  CALL("AIG::Ref::getFreeVars");
  return node()->getFreeVars();
}

/**
 * Return sort of a variable in the AIG.
 * Variable must appear in the AIG.
 * Careful, time may be linear with the depth of the AIG.
 */
unsigned AIG::Ref::getVarSort(unsigned var) const
{
  CALL("AIG::Ref::getVarSort");
  ASS(getFreeVars()->member(var));

  AIGRef a = *this;
  while(!a.isAtom()) {
    switch(node()->kind()) {
    case Node::QUANT:
      a = a.parent(0);
      break;
    case Node::CONJ:
    {
      AIGRef p1 = a.parent(0);
      AIGRef p2 = a.parent(1);
      bool firstHas = p1.getFreeVars()->member(var);
      bool secondHas = p2.getFreeVars()->member(var);
      if(!firstHas) {
	ASS(secondHas);
	a = p2;
      }
      else if(!secondHas) {
	a = p1;
      }
      else {
	//both have the variable, so we just take the more convenient one
	//(nodes with lower indexes are somehow expected to be simpler)
	if(p1.isAtom() || p1.nodeIndex()<p2.nodeIndex()) {
	  a = p1;
	}
	else {
	  a = p2;
	}
      }
      break;
    }
    case Node::ATOM:
    case Node::TRUE_CONST:
    default:
      ASSERTION_VIOLATION;
    }
  }
  return SortHelper::getVariableSort(TermList(var,false),a.getPositiveAtom());
}


Color AIG::Ref::getColor() const
{
  CALL("AIG::Ref::getColor");
  return node()->getColor();
}

unsigned AIG::Ref::nodeIndex() const
{
  CALL("AIG::Ref::nodeIndex");

  return node()->nodeIdx();
}

/**
 * Return number of parent AIG nodes
 */
unsigned AIG::Ref::parentCnt() const
{
  CALL("AIG::Ref::parentCnt");

  switch(node()->kind()) {
  case Node::TRUE_CONST:
  case Node::ATOM:
    return 0;
  case Node::QUANT:
    return 1;
  case Node::CONJ:
    return 2;
  default:
    ASSERTION_VIOLATION;
  }
}

/**
 * Return @c idx-th parent.
 *
 * Precondition:
 * 	idx < parentCnt()
 */
AIG::Ref AIG::Ref::parent(unsigned idx) const
{
  CALL("AIG::Ref::parent");

  switch(node()->kind()) {
  case Node::QUANT:
    ASS_EQ(idx,0);
    return node()->qParent();
  case Node::CONJ:
    ASS_L(idx,2);
    return node()->parent(idx);
  case Node::TRUE_CONST:
  case Node::ATOM:
  default:
    ASSERTION_VIOLATION;
  }
}


unsigned AIG::Ref::hash() const
{
  return node()->nodeIdx()*2 + polarity();
}

bool AIG::Ref::operator<(const Ref& r) const
{
  CALL("AIG::Ref::operator<");
  Node* n1 = node();
  Node* n2 = r.node();
  if(n1!=n2) {
    ASS_NEQ(n1->nodeIdx(),n2->nodeIdx());
    return n1->nodeIdx()<n2->nodeIdx();
  }
  if(polarity() && !r.polarity()) {
    return true;
  }
  return false;
}

string AIG::Ref::toString() const
{
  CALL("AIG::Ref::toString");

  string inner;
  switch(node()->kind()) {
  case Node::TRUE_CONST:
    return polarity() ? "$true" : "$false";
  case Node::ATOM:
    inner = node()->literal()->toString();
    break;
  case Node::CONJ:
    inner = '(' + node()->parent(0).toString() + " & " + node()->parent(1).toString() + ')';
    break;
  case Node::QUANT:
  {
    inner = "! [";
    VarSet::Iterator vit(*node()->qVars());
    while(vit.hasNext()) {
      int var = vit.next();
      inner += 'X'+Int::toString(var);
      if(vit.hasNext()) {
	inner += ',';
      }
    }
    inner += "] : " + node()->qParent().toString();
    break;
  }
  default:
    ASSERTION_VIOLATION;
  }
  return (polarity() ? "" : "~") + inner;
}

/**
 * Output string representation of AIG that reveals links to parent AIGs
 */
string AIG::Ref::toInternalString(unsigned depth) const
{
  string inner;

  Node::Kind kind = node()->kind();

  if(kind==Node::TRUE_CONST) {
    return polarity() ? "$true" : "$false";
  }

  if(kind==Node::ATOM) {
    inner = node()->literal()->toString();
  }
  else if(depth==0) {
    inner = Int::toString(node()->nodeIdx());
  }
  else {
    inner = Int::toString(node()->nodeIdx()) + ": ";
    switch(node()->kind()) {
    case Node::CONJ:
      inner += '(' + node()->parent(0).toInternalString(depth-1) + " & " + node()->parent(1).toInternalString(depth-1) + ')';
      break;
    case Node::QUANT:
    {
      inner += "! [";
      VarSet::Iterator vit(*node()->qVars());
      while(vit.hasNext()) {
        int var = vit.next();
        inner += 'X'+Int::toString(var);
        if(vit.hasNext()) {
          inner += ',';
        }
      }
      inner += "] : " + node()->qParent().toInternalString(depth-1);
      break;
    }
    default:
      ASSERTION_VIOLATION;
    }
  }

  return (polarity() ? "" : "~") + inner;
}


AIG::AIG() : _simplLevel(3), _nextNodeIdx(0), _conjReserve(0), _quantReserve(0)
{
  CALL("AIG::AIG");
  _trueNode = new Node(Node::TRUE_CONST);
  _trueNode->setNodeIdx(_nextNodeIdx++);
  _trueNode->setPrecomputedValues();
  _orderedNodeRefs.push(Ref(_trueNode, true));
}

AIG::~AIG()
{
  if(_conjReserve) {
    delete _conjReserve;
  }
  if(_quantReserve) {
    delete _quantReserve;
  }
  NodeSet::Iterator nsIt(_compNodes);
  while(nsIt.hasNext()) {
    delete nsIt.next();
  }
  AtomNodeMap::Iterator anIt(_atomNodes);
  while(anIt.hasNext()) {
    Node* n = anIt.next();
    delete n;
  }
  delete _trueNode;
}

AIG::Node* AIG::atomNode(Literal* positiveLiteral)
{
  CALL("AIG::atomNode");
  ASS(positiveLiteral->isPositive());

  Node* res;
  if(_atomNodes.find(positiveLiteral, res)) {
    return res;
  }
  res = new Node(positiveLiteral);
  res->setNodeIdx(_nextNodeIdx++);
  res->setPrecomputedValues();
  _atomNodes.insert(positiveLiteral, res);
  _orderedNodeRefs.push(Ref(res, true));
  return res;
}

void AIG::normalizeRefOrder(Ref& par1, Ref& par2)
{
  CALL("AIG::normalizeRefOrder");
  if(par1>par2) {
    swap(par1,par2);
  }
}

AIG::Node* AIG::conjNode(Ref par1, Ref par2)
{
  CALL("AIG::conjNode");
  if(!_conjReserve) {
    _conjReserve = new Node(Node::CONJ);
  }
  normalizeRefOrder(par1,par2);
  _conjReserve->setConjParents(par1,par2);
  Node* res = _compNodes.insert(_conjReserve);
  if(res==_conjReserve) {
    //we have used the reserve
    _conjReserve = 0;
    res->setNodeIdx(_nextNodeIdx++);
    res->setPrecomputedValues();
    _orderedNodeRefs.push(Ref(res, true));
  }
  return res;
}

AIG::Node* AIG::univQuantNode(VarSet* vars, Ref par)
{
  CALL("AIG::univQuantNode");
  ASS(vars);
  ASS_GE(vars->size(),1);

  if(!_quantReserve) {
    _quantReserve = new Node(Node::QUANT);
  }
  _quantReserve->setQuantArgs(vars, par);
  Node* res = _compNodes.insert(_quantReserve);
  if(res==_quantReserve) {
    //we have used the reserve
    _quantReserve = 0;
    res->setNodeIdx(_nextNodeIdx++);
    res->setPrecomputedValues();
    _orderedNodeRefs.push(Ref(res, true));
  }
  return res;
}

AIG::Ref AIG::getLit(Literal* lit)
{
  CALL("AIG::getLit");

  if(lit->isPositive()) {
    return Ref(atomNode(lit), true);
  }
  Literal* posLit = Literal::complementaryLiteral(lit);
  return Ref(atomNode(posLit), false);
}

AIG::Ref AIG::getConj(Ref par1, Ref par2)
{
  CALL("AIG::getConj");

start:
  if(_simplLevel>=1) {
    Ref res;
    if(tryO1ConjSimpl(par1, par2, res)) { return res; }
    if(_simplLevel>=2) {
      if(tryO2ConjSimpl(par1, par2, res)) { return res; }
      if(_simplLevel>=3) {
	if(tryO3ConjSimpl(par1, par2)) {
	  //tryO3ConjSimpl has updated the parent references,
	  //so we rerun the simplifications with them
	  goto start;
	}
	if(_simplLevel>=4) {
	  if(tryO4ConjSimpl(par1, par2)) {
	    //tryO4ConjSimpl has updated the parent references,
	    //so we rerun the simplifications with them
	    goto start;
	  }
	}
      }
    }
  }

  return Ref(conjNode(par1, par2), true);
}

AIG::Ref AIG::getQuant(bool exQuant, Formula::VarList* vars, Ref par)
{
  CALL("AIG::getQuant(bool,VarList*,Ref)");

  VarSet* vs = VarSet::getFromIterator(Formula::VarList::DestructiveIterator(vars));
  return getQuant(exQuant, vs, par);
}

AIG::Ref AIG::getUnivQuant(VarSet* vars0, Ref par)
{
  CALL("AIG::getUnivQuant");

  //we try to merge quantifiers where possible
  if(par.isQuantifier() && par.polarity()) {
    VarSet* vars = vars0->getUnion(par.getQuantifierVars());
    //this seems possibly recursive, but we can do this recursive call at most once
    return getUnivQuant(vars, par.parent(0));
  }

  VarSet* vars = vars0->getIntersection(par.getFreeVars());

  if(vars->isEmpty()) { return par; }

  return Ref(univQuantNode(vars, par), true);
}

AIG::Ref AIG::getQuant(bool exQuant, VarSet* vars0, Ref par)
{
  CALL("AIG::getQuant(bool,VarSet*,Ref)");

  if(exQuant) {
    return getUnivQuant(vars0, par.neg()).neg();
  }
  else {
    return getUnivQuant(vars0, par);
  }
}

bool AIG::tryO1ConjSimpl(Ref par1, Ref par2, Ref& res)
{
  CALL("AIG::tryO1ConjSimpl");
  if(par2.isPropConst()) {
    swap(par1,par2);
  }
  if(par1.isPropConst()) {
    if(par1.isTrue()) {
      res = par2; // (a /\ T) ---> a
    }
    else {
      ASS(par1.isFalse());
      res = par1; // (a /\ F) ---> F
    }
    return true;
  }
  if(par1.node()==par2.node()) {
    if(par1.polarity()==par2.polarity()) {
      res = par1; // (a /\ a) ---> a
    }
    else {
      res = getFalse(); // (a /\ ~a) ---> F
    }
    return true;
  }
  return false;
}
bool AIG::tryO2ConjSimpl(Ref par1, Ref par2, Ref& res)
{
  CALL("AIG::tryO2ConjSimpl");

  if(tryO2AsymetricConjSimpl(par1, par2, res)) { return true; }
  return tryO2AsymetricConjSimpl(par2, par1, res);
}
bool AIG::tryO2AsymetricConjSimpl(Ref par1, Ref par2, Ref& res)
{
  CALL("AIG::tryO2AsymetricConjSimpl");

  Node* pn1 = par1.node();
  if(pn1->kind()!=Node::CONJ) { return false; }

  Ref gp11 = pn1->parent(0);
  Ref gp12 = pn1->parent(1);
  if(par1.polarity()) {
    if(gp11.neg()==par2 || gp12.neg()==par2) {
      res = getFalse(); // (a /\ b) /\ c [a!=c | b!=c] ---> F
      return true;
    }
    if(gp11==par2 || gp12==par2) {
      res = par1; // (a /\ b) /\ c [a=c | b=c] ---> (a /\ b)
      return true;
    }
  }
  else {
    if(gp11.neg()==par2 || gp12.neg()==par2) {
      res = par2; // ~(a /\ b) /\ c [a!=c | b!=c] ---> c
      return true;
    }
  }

  Node* pn2 = par2.node();
  if(pn2->kind()!=Node::CONJ) { return false; }
  Ref gp21 = pn2->parent(0);
  Ref gp22 = pn2->parent(1);

  if(par1.polarity()) {
    //we've added the check on node index ordering, because we don't need
    //to perform this particular check twice
    if(par2.polarity() && pn1->nodeIdx()<pn2->nodeIdx()) {
      if(gp11.neg()==gp21 || gp11.neg()==gp22 || gp12.neg()==gp21 || gp12.neg()==gp22) {
	res = getFalse(); // (a /\ b) /\ (c /\ d) [a!=c | a!=d | b!=c | b!=d] ---> F
	return true;
      }
    }
  }
  else {
    if(par2.polarity()) {
      if(gp11.neg()==gp21 || gp11.neg()==gp22 || gp12.neg()==gp21 || gp12.neg()==gp22) {
	res = par2; // ~(a /\ b) /\ (c /\ d) [a!=c | a!=d | b!=c | b!=d] ---> c /\ d
	return true;
      }
    }
    else {
      if((gp11==gp22 && gp12.neg()==gp21) || (gp11==gp21 && gp12.neg()==gp22)) {
	res = gp11.neg(); // ~(a /\ b) /\ ~(c /\ d) [a=d & b!=c] ---> ~a
	return true;
      }
    }
  }
  return false;
}
/**
 * O3 simplifications create one new node which may require simplifications itself.
 * We therefore let O3 simplifications modify the parameters and if they do, we
 * rerun the simplifications starting from O1.
 */
bool AIG::tryO3ConjSimpl(Ref& par1, Ref& par2)
{
  CALL("AIG::tryO3ConjSimpl");

  if(tryO3AsymetricConjSimpl(par1, par2)) { return true; }
  return tryO3AsymetricConjSimpl(par2, par1);
}
bool AIG::tryO3AsymetricConjSimpl(Ref& par1, Ref& par2)
{
  CALL("AIG::tryO3AsymetricConjSimpl");

  if(par1.polarity()) { return false; }

  Node* pn1 = par1.node();
  if(pn1->kind()!=Node::CONJ) { return false; }

  Ref gp11 = pn1->parent(0);
  Ref gp12 = pn1->parent(1);

  if(gp12==par2) {
    par1 = gp11.neg(); // ~(a /\ b) /\ c [b=c] ---> ~a /\ c
    return true;
  }
  if(gp11==par2) {
    par1 = gp12.neg(); // ~(a /\ b) /\ c [a=c] ---> ~b /\ c
    return true;
  }

  if(!par2.polarity()) { return false; }

  Node* pn2 = par2.node();
  if(pn2->kind()!=Node::CONJ) { return false; }
  Ref gp21 = pn2->parent(0);
  Ref gp22 = pn2->parent(1);

  if(gp12==gp21 || gp12==gp22) {
    par1 = gp11.neg(); // ~(a /\ b) /\ (c /\ d) [b=c | a=d] ---> ~a /\ (c /\ d)
    return true;
  }
  if(gp11==gp21 || gp11==gp22) {
    par1 = gp12.neg(); // ~(a /\ b) /\ (c /\ d) [a=c | a=d] ---> ~b /\ (c /\ d)
    return true;
  }

  return false;
}
bool AIG::tryO4ConjSimpl(Ref& par1, Ref& par2)
{
  CALL("AIG::tryO4ConjSimpl");
  NOT_IMPLEMENTED;
}

void AIG::collectConjuncts(AIGRef aig, AIGStack& acc)
{
  CALL("AIG::collectConjuncts");

  static AIGStack toDo;
  toDo.reset();
  toDo.push(aig);
  while(toDo.isNonEmpty()) {
    AIGRef a = toDo.pop();
    if(!a.polarity() || !a.isConjunction()) {
      acc.push(a);
      continue;
    }
    toDo.push(a.parent(0));
    toDo.push(a.parent(1));
  }
}

void AIG::flattenConjuncts(AIGStack& conjuncts)
{
  CALL("AIG::flattenConjuncts");

  static AIGStack unprocessed;
  unprocessed.reset();

  AIGStack::DelIterator ait(conjuncts);
  while(ait.hasNext()) {
    AIGRef cur = ait.next();
    if(cur.isConjunction() && cur.polarity()) {
      unprocessed.push(cur);
      ait.del();
    }
  }

  while(unprocessed.isNonEmpty()) {
    collectConjuncts(unprocessed.pop(), conjuncts);
  }
}

AIGRef AIG::makeConjunction(const AIGStack& conjuncts)
{
  CALL("AIG::makeConjunction");

  if(conjuncts.isEmpty()) {
    return getTrue();
  }

  static AIGStack conjNorm;
  conjNorm = conjuncts;

  std::sort(conjNorm.begin(), conjNorm.end());

  AIGRef res = conjNorm.pop();
  while(conjNorm.isNonEmpty()) {
    res = getConj(res, conjNorm.pop());
  }
  return res;
}


////////////////////////////
// AIGInsideOutPosIterator
//

void AIGInsideOutPosIterator::reset(AIGRef a)
{
  CALL("AIGInsideOutPosIterator::reset");

  _ready = false;
  _seen.reset();
  _stack.reset();
  if(a.isValid()) {
    _stack.push(a.getPositive());
  }
}

/**
 * Add unvisited sub-aigs (including a itself) into the traversal.
 * This function can be called at any point and will cause the
 * next retrieved item to belong to @c a (if some of it is yet to
 * be traversed).
 */
void AIGInsideOutPosIterator::addToTraversal(AIGRef a)
{
  CALL("AIGInsideOutPosIterator::addToTraversal");

  a = a.getPositive();
  if(!_seen.find(a)) {
    bool wasReady = _ready;
    _stack.push(a);
    if(wasReady) {
      _ready = false;
      ALWAYS(hasNext());
    }
  }
}

bool AIGInsideOutPosIterator::hasNext() {
  CALL("AIGInsideOutPosIterator::hasNext");

  if(_ready) { return true; }
  if(_stack.isEmpty()) { return false; }
  while(_stack.isNonEmpty()) {
    AIGRef curr = _stack.top();
    unsigned parCnt = curr.parentCnt();
    for(unsigned i=0; i<parCnt; i++) {
      AIGRef ppar = curr.parent(i).getPositive();
      if(!_seen.find(ppar)) {
        _stack.push(ppar);
      }
    }
    if(_stack.top()==curr) {
      if(_seen.insert(curr)) {
	_ready = true;
	return true;
      }
      else {
	_stack.pop();
      }
    }
  }
  //without calling the addToTraversal() function, this point should be unreachable
  return false;
}

AIGRef AIGInsideOutPosIterator::next()
{
  CALL("AIGInsideOutPosIterator::next");
  ASS(_ready);
  ASS(_stack.top().polarity());

  _ready = false;
  return _stack.pop();
}

///////////////////////
// AIGTransformer
//

/**
 * Iteratively dereference r in map, not looking at its child
 * nodes (hence level 0).
 * Even though only positve references are allowed in the map,
 * this function handles also negative ones.
 */
AIG::Ref AIGTransformer::lev0Deref(Ref r, DHMap<Ref,Ref>& map)
{
  CALL("AIGTransformer::lev0Deref");

  static Stack<pair<Ref,bool> > queries;
  queries.reset();

  bool resNeg = false;

  for(;;) {

    bool neg = !r.polarity();
    if(neg) {
      resNeg = !resNeg;
      r = r.neg();
    }

    Ref tgt;
    if(!map.find(r, tgt) || r==tgt) {
      break;
    }
    queries.push(make_pair(r,resNeg));
    ASS_LE(queries.size(), map.size());
    r = tgt;
  }

  if(queries.isNonEmpty()) {
    //we compress the dereference chain
    queries.pop();
    while(queries.isNonEmpty()) {
      pair<Ref,bool> rec = queries.pop();
      Ref toCache = (rec.second==resNeg) ? r : r.neg();
      //DHMap::set returns false when overwriting
      NEVER(map.set(rec.first, toCache));
    }
  }

  return resNeg ? r.neg() : r;
}

/**
 * (Iteratively) dereference parents of r in map
 *
 * r must be level 0 dereferenced.
 */
AIG::Ref AIGTransformer::lev1Deref(Ref r, RefMap& map)
{
  CALL("AIGTransformer::lev1Deref");
  ASS_EQ(r, lev0Deref(r, map));

  bool neg = !r.polarity();
  if(neg) {
    r = r.neg();
  }

  Node* n = r.node();
  Ref res;
  switch(n->kind()) {
  case Node::ATOM:
  case Node::TRUE_CONST:
    res = r;
    break;
  case Node::CONJ:
  {
    Ref p1 = n->parent(0);
    Ref p2 = n->parent(1);
    Ref dp1 = lev0Deref(p1, map);
    Ref dp2 = lev0Deref(p2, map);
    if(p1==dp1 && p2==dp2) {
      res = r;
    }
    else {
      res = _aig.getConj(dp1, dp2);
    }
    break;
  }
  case Node::QUANT:
  {
    Ref p = n->qParent();
    Ref dp = lev0Deref(p, map);
    if(p==dp) {
      res = r;
    }
    else {
      res = _aig.getQuant(false, n->qVars(), dp);
    }
    break;
  }
  }

  return neg ? res.neg() : res;
}

/**
 * Make elements on the stack positive references and add positive references
 * to their AIG predecessors
 *
 * The order of elements on the stack is arbitrary.
 */
void AIGTransformer::addAIGPredecessors(AIGStack& stack)
{
  CALL("AIGTransformer::addAIGPredecessors");

  static DHSet<Ref> seen;
  seen.reset();
  static AIGStack toDo;
  toDo.reset();
  toDo.loadFromIterator(AIGStack::Iterator(stack));
  stack.reset();

  while(toDo.isNonEmpty()) {
    Ref r = toDo.pop();
    if(!r.polarity()) { r = r.neg(); }

    if(seen.contains(r)) { continue; }
    seen.insert(r);

    stack.push(r);

    Node* n = r.node();
    switch(n->kind()) {
    case Node::ATOM:
    case Node::TRUE_CONST:
      break;
    case Node::QUANT:
      toDo.push(n->qParent());
      break;
    case Node::CONJ:
      toDo.push(n->parent(0));
      toDo.push(n->parent(1));
      break;
    default:
      ASSERTION_VIOLATION;
    }
  }
}

void AIGTransformer::collectUsed(Ref r, const RefMap& map, RefEdgeMap& edges)
{
  CALL("AIGTransformer::collectUsed");
  ASS(r.polarity());
  ASS(map.find(r));

  static Stack<Ref> preds;
  preds.reset();
  preds.push(map.get(r));
  addAIGPredecessors(preds);

  Stack<Ref>::Iterator it(preds);
  while(it.hasNext()) {
    Ref p = it.next();
    if(map.find(p) && p!=r) {
      if (env.options->showPreprocessing()) {
        env.beginOutput();
        env.out() << "[PP] aigtr_sat dep: " << r << " <-- " << p << std::endl;
        env.endOutput();
      }
      edges.pushToKey(r, p);
    }
  }
}

/**
 * Order Refs in the stack so that later can refer only to earlier
 *
 * Currently we use a simple n.log n sort by node indexes, if this
 * shows to be a bottle neck, one can use linear topological sorting.
 */
void AIGTransformer::orderTopologically(AIGStack& stack)
{
  CALL("AIGTransformer::orderTopologically");

  std::sort(stack.begin(), stack.end());
}

void AIGTransformer::saturateOnTopSortedStack(const AIGStack& stack, RefMap& map)
{
  CALL("AIGTransformer::saturateOnTopSortedStack");

  unsigned idx = 0;
  //we have to iterate by indexes because the stack may be modified
  //and therefore we cannot use an iterator
  //(the stack may be modified as we can use _aig._orderedNodeRefs stack
  //where newly created nodes are added)
  for(size_t stack_idx = 0; stack_idx<stack.size(); stack_idx++) {
    Ref r = stack[stack_idx];
    ++idx;
    Ref dr0 = lev0Deref(r, map);
    ASS_EQ(lev0Deref(dr0, map), dr0);
    Ref dr1 = lev1Deref(dr0, map);
    if(r==dr1) {
      //nothing in the map applies
      continue;
    }
#if 1 //maybe it is not necessary to achieve the following condition:
    //if the node is dereferenced in the map, the parents of
    //the node should already be dereferenced as well
    ASS(r==dr0 || dr0==dr1);
#endif
    if(dr0==dr1) {
      ASS_EQ(map.get(r),dr1);
    }
    else {
      map.insert(r,dr1);
    }
  }
}

/**
 * Make elements on the stack positive references and add positive references
 * to their AIG predecessors. Order the elements on the stack so that
 * elements can refer only to elements closer to the stack bottom.
 */
void AIGTransformer::makeOrderedAIGGraphStack(AIGStack& stack)
{
  CALL("AIGTransformer::makeOrderedAIGGraphStack");

  addAIGPredecessors(stack);
  orderTopologically(stack);
}

/**
 * Apply @c map on @c r0 with caching (so that after the function returns,
 * map[r0] will be defined.
 *
 * To obtain predictable results, @c map should be idempotent.
 */
void AIGTransformer::applyWithCaching(Ref r0, RefMap& map)
{
  CALL("AIGTransformer::applyWithCaching");
  if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] applyWithCaching -- "<<r0 << std::endl;
    env.endOutput();
  }
  static Stack<Ref> toDo;
  toDo.reset();

  toDo.push(r0);
  makeOrderedAIGGraphStack(toDo);

  ASS_EQ(toDo.top().node(), r0.node());
  saturateOnTopSortedStack(toDo, map);
}

/**
 * @param map in/out, map that is restricted to become acyclic
 * @param domainOrder out parameter, will receive domain elements
 *        of the restricted map in topological order (nodes can refer
 *        only to items closer to the bottom of the stack).
 */
void AIGTransformer::restrictToGetOrderedDomain(RefMap& map, AIGStack& domainOrder)
{
  CALL("AIGTransformer::restrictToGetOrderedDomain");

  if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] ordering domain" << std::endl;
    env.endOutput();
  }

  static DHSet<Ref> seen;
  seen.reset();

  typedef MapToLIFOGraph<Ref> RefGraph;
  typedef Subgraph<RefGraph> RefSubgraph;
  RefGraph::Map edgeMap;

  VirtualIterator<Ref> domIt = map.domain();

  while(domIt.hasNext()) {
    Ref d = domIt.next();
    if (env.options->showPreprocessing()) {
      env.beginOutput();
      env.out() << "[PP] aigtr_inp_map: " << d<<" --> "<<map.get(d) << std::endl;
      env.endOutput();
    }
    collectUsed(d, map, edgeMap);
  }

  RefGraph gr(edgeMap);
  gr.ensureNodes(map.domain());

  SCCAnalyzer<RefGraph> an0(gr);
  ScopedPtr<SCCAnalyzer<RefSubgraph> > an1;
  if(an0.breakingNodes().isNonEmpty()) {
    //if we have circular dependencies, we fix them by removing some mappings
    AIGStack::ConstIterator brIt(an0.breakingNodes());
    while(brIt.hasNext()) {
      Ref br = brIt.next();
      if (env.options->showPreprocessing()) {
        env.beginOutput();
        env.out() << "[PP] domain element removed to break cycles: "<<br << std::endl;
        env.endOutput();
      }      
      map.remove(br);
    }
    Subgraph<RefGraph> subGr(gr, AIGStack::ConstIterator(an0.breakingNodes()));
    an1 = new SCCAnalyzer<RefSubgraph>(subGr);
  }

  const Stack<AIGStack>& comps = an1 ? an1->components() : an0.components();
  Stack<AIGStack>::BottomFirstIterator cit(comps);
  while(cit.hasNext()) {
    const AIGStack& comp = cit.next();
    ASS_EQ(comp.size(),1);
    domainOrder.push(comp.top());
    if (env.options->showPreprocessing()) {
      env.beginOutput();
      env.out() << "[PP] domain element to process: "<<comp.top() << std::endl;
      env.endOutput();
    }
  }
}

void AIGTransformer::makeIdempotent(DHMap<Ref,Ref>& map, Stack<Ref>* finalDomain)
{
  CALL("AIGTransformer::makeIdempotent");

  static AIGStack order;
  order.reset();
  restrictToGetOrderedDomain(map, order);
  AIGStack::BottomFirstIterator cit(order);
  while(cit.hasNext()) {
    Ref r = cit.next();
    applyWithCaching(map.get(r), map);
    lev0Deref(r, map); //collapse the rewritings
    if(finalDomain) {
      finalDomain->push(r);
    }
  }
}

/**
 * Given map from AIG node --> AIG node, extend it to all nodes
 * that contain the given ones.
 * If map is not acyclic, remove some rewrites to make it acyclic.
 * Domain of map must only contain AIGRefs with positive polarity.
 *
 * @param map the map
 * @param finalDomain if non-zero, Refs that weren't eliminated from
 *                    the map wil be added into the stack.
 */
void AIGTransformer::saturateMap(DHMap<Ref,Ref>& map, Stack<Ref>* finalDomain)
{
  CALL("AIGTransformer::saturateMap");
  ASS_REP(forAll(map.domain(), AIG::hasPositivePolarity), getFirstTrue(map.domain(), negPred(AIG::hasPositivePolarity)));

  makeIdempotent(map, finalDomain);

  saturateOnTopSortedStack(_aig._orderedNodeRefs, map);
}

///////////////////////
// AIGFormulaSharer
//

AIGFormulaSharer::AIGFormulaSharer() : _transf(_aig), _useRewrites(false)
{
  shareFormula(Formula::trueFormula(), _aig.getTrue());
  shareFormula(Formula::falseFormula(), _aig.getFalse());
}

void AIGFormulaSharer::apply(Problem& prb)
{
  CALL("AIGFormulaSharer::apply");

  if(apply(prb.units())) {
    prb.invalidateByRemoval();
  }
}

bool AIGFormulaSharer::apply(UnitList*& units)
{
  CALL("AIGFormulaSharer::apply(UnitList*&)");

  bool modified = false;

  UnitList::DelIterator uit(units);
  while(uit.hasNext()) {
    Unit* u = uit.next();
    if(u->isClause()) {
      continue;
    }
    FormulaUnit* fu = static_cast<FormulaUnit*>(u);
    FormulaUnit* newUnit = 0;
    if(!apply(fu, newUnit)) {
      continue;
    }
    uit.replace(newUnit);
    modified = true;
  }

  return modified;
}

Formula* AIGFormulaSharer::shareFormula(Formula* f, AIGRef aig)
{
  CALL("AIGFormulaSharer::shareFormula");

  Formula** pRes;
  if(_formReprs.getValuePtr(aig, pRes)) {
    if (env.options->showPreprocessing()) {
      env.beginOutput();
      env.out() << "[PP] aig_a2f_sharing: (aig,formula) pair added to sharing:"<<endl<<
                  "  aig: "<<aig<<endl<<
                	"  frm: "<<(*f) << std::endl;
      env.endOutput();
    }    
    *pRes = f;
    ALWAYS(_formAIGs.insert(f, aig));
  }
  return *pRes;
}

/**
 * If necessary subnodes are present in the sharing structure,
 * add formula representation of quantifier AIG node @c a into
 * the sharing structure.
 * Otherwise push @c a followed by necessary subnodes on the
 * @c toBuild stack.
 */
void AIGFormulaSharer::buildQuantAigFormulaRepr(AIGRef a, Stack<AIGRef>& toBuild)
{
  CALL("AIGFormulaSharer::buildQuantAigFormulaRepr");

  bool pol = a.polarity();
  AIG::Node* n = a.node();
  ASS_EQ(n->kind(), AIG::Node::QUANT);

  AIGRef subnode;
  if(pol) {
    // we'll build universal quantifier
    subnode = n->qParent();
  }
  else {
    // we'll build existential quantifier
    subnode = n->qParent().neg();
  }

  Formula* subForm;
  if(!_formReprs.find(subnode, subForm)) {
    toBuild.push(a);
    toBuild.push(subnode);
    return;
  }
  Formula::VarList* qVars = 0;
  Formula::VarList::pushFromIterator(AIG::VarSet::Iterator(*n->qVars()), qVars);
  shareFormula(new QuantifiedFormula(pol ? FORALL : EXISTS, qVars, subForm), a);
}

bool AIGFormulaSharer::tryBuildEquivalenceFormulaRepr(AIGRef aig, Stack<AIGRef>& toBuild)
{
  CALL("AIGFormulaSharer::tryBuildEquivalenceFormulaRepr");

  if(!aig.isConjunction()) { return false; }

  AIGRef p1 = aig.parent(0);
  AIGRef p2 = aig.parent(1);

  if(!p1.isConjunction() || !p2.isConjunction()) { return false; }

  AIGRef p11 = p1.parent(0);
  AIGRef p12 = p1.parent(1);
  AIGRef p21 = p2.parent(0);
  AIGRef p22 = p2.parent(1);

  if(p11.getPositive()!=p21.getPositive()) {
    swap(p21, p22);
  }
  if(p11.getPositive()!=p21.getPositive()) {
    return false;
  }
  if(p12.getPositive()!=p22.getPositive()) {
    return false;
  }
  if(p11.polarity()==p21.polarity() || p12.polarity()==p22.polarity()) {
    return false;
  }

  if(p1.polarity() || p2.polarity()) {
    return false;
  }

  bool neg = !aig.polarity();

  //if neg==false, we have               //
  //         and                         //
  //       /     \                       //
  //     or       or                     //
  //    /  \     /  \                    //
  // ~p11  p22 p11  ~p22                 //
  // which is equivalence p11 <=> p22

  //if neg==true, we have                //
  //          or                         //
  //       /     \                       //
  //     and      and                    //
  //    /  \     /  \                    //
  //  p11  p12 ~p11  ~p12                //
  // which is equivalence p11 <=> p12    //

  AIGRef eqAIGs[2] = {p11, neg ? p12 : p22};
  Formula* subForms[2] = {0,0};
  _formReprs.find(eqAIGs[0], subForms[0]);
  _formReprs.find(eqAIGs[1], subForms[1]);
  if(!subForms[0] || !subForms[1]) {
    toBuild.push(aig);
    if(!subForms[0]) {
      toBuild.push(eqAIGs[0]);
    }
    if(!subForms[1]) {
      toBuild.push(eqAIGs[1]);
    }
    return true;
  }
  shareFormula(new BinaryFormula(IFF, subForms[0], subForms[1]), aig);
  return true;
}

/**
 * If necessary subnodes are present in the sharing structure,
 * add formula representation of conjunction AIG node @c a into
 * the sharing structure.
 * Otherwise push @c a followed by necessary subnodes on the
 * @c toBuild stack.
 */
void AIGFormulaSharer::buildConjAigFormulaRepr(AIGRef a, Stack<AIGRef>& toBuild)
{
  CALL("AIGFormulaSharer::buildConjAigFormulaRepr");

  if(tryBuildEquivalenceFormulaRepr(a, toBuild)) {
    return;
  }

  bool pol = a.polarity();
#if 1
  static AIGStack members;
  members.reset();
  _aig.collectConjuncts(a.getPositive(), members);

  static FormulaStack forms;
  forms.reset();
  bool someMissing = false;

  AIGStack::Iterator mit(members);
  while(mit.hasNext()) {
    AIGRef mBase = mit.next();
    AIGRef member = pol ? mBase : mBase.neg();

    Formula* form;
    if(_formReprs.find(member, form)) {
      forms.push(form);
    }
    else {
      if(!someMissing) {
	toBuild.push(a);
	someMissing = true;
      }
      toBuild.push(member);
    }
  }

  if(someMissing) {
    return;
  }

  FormulaList* args = 0;
  FormulaList::pushFromIterator(FormulaStack::TopFirstIterator(forms), args);
#else
  AIG::Node* n = a.node();
  ASS_EQ(n->kind(), AIG::Node::CONJ);

  AIGRef pars[2];
  if(pol) {
    // we'll build conjunction
    pars[0] = n->parent(0);
    pars[1] = n->parent(1);
  }
  else {
    // we'll build disjunction
    pars[0] = n->parent(0).neg();
    pars[1] = n->parent(1).neg();
  }

  Formula* subForms[2] = {0,0};
  _formReprs.find(pars[0], subForms[0]);
  _formReprs.find(pars[1], subForms[1]);
  if(!subForms[0] || !subForms[1]) {
    toBuild.push(a);
    if(!subForms[0]) {
      toBuild.push(pars[0]);
    }
    if(!subForms[1]) {
      toBuild.push(pars[1]);
    }
    return;
  }
  FormulaList* args = new FormulaList(subForms[0], new FormulaList(subForms[1], 0));
#endif
  shareFormula(new JunctionFormula(pol ? AND : OR, args), a);
}


Formula* AIGFormulaSharer::aigToFormula(AIGRef aig0)
{
  CALL("AIGFormulaSharer::aigToFormula");

  Formula* res;
  if(_formReprs.find(aig0, res)) {
    if (env.options->showPreprocessing()) {
      env.beginOutput();
      env.out() << "[PP] aig_a2f_cached: whole aig with cached formula: "
              <<aig0<<" --> "<<(*res) << std::endl;
      env.endOutput();
    }    
    return res;
  }

  static Stack<AIGRef> toBuild;
  toBuild.reset();
  toBuild.push(aig0);

  while(toBuild.isNonEmpty()) {
    AIGRef a = toBuild.pop();

    if(_formReprs.find(a)) {
      if (env.options->showPreprocessing()) {
        env.beginOutput();
        env.out() << "[PP] aig_a2f_cached: aig with cached formula: "
                <<a<<" --> "<<(*_formReprs.get(a)) << std::endl;
        env.endOutput();
      }      
      continue;
    }

    Formula* form;

    if(a.isQuantifier() || a.isConjunction()) {
      Formula* negRes;
      if(!_formReprs.find(a.neg(), negRes)) {

	//building of conjucntions and quantifiers can generate further subtasks
	if(a.isQuantifier()) {
	  buildQuantAigFormulaRepr(a, toBuild);
	}
	else {
	  ASS(a.isConjunction());
	  buildConjAigFormulaRepr(a, toBuild);
	}
	continue; //continue for the outmost while loop

      }
      else {
	//if a negated formula is shared, the negation argument would also be shared and have aig equal to a
	ASS_NEQ(negRes->connective(), NOT);
	form = new NegatedFormula(negRes);
      }
    }
    else if(a.isAtom()) {
      Literal* posLit = a.getPositiveAtom();
      Literal* lit = a.polarity() ? posLit : Literal::complementaryLiteral(posLit);
      form = new AtomicFormula(lit);
    }
    if(a.isPropConst()) {
      form = a.polarity() ? Formula::trueFormula() : Formula::falseFormula();
    }
    if (env.options->showPreprocessing()) {
      env.beginOutput();
      env.out() << "[PP] aig_a2f_new: aig with newly created formula: "
              <<a<<" --> "<<(*form) << std::endl;
      env.endOutput();
    }
    shareFormula(form, a);

  }
  return _formReprs.get(aig0);
}

bool AIGFormulaSharer::apply(FormulaUnit* unit, FormulaUnit*& res)
{
  CALL("AIGFormulaSharer::apply(Unit*,Unit*&)");

  Formula* f0 = unit->formula();
  ARes ar = apply(f0);
  Formula* f = ar.first;

  if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] aig_nodes: " << (*unit) << " has AIG node " 
            << ar.second.toString() << std::endl;
    env.endOutput();
  }  

  if(f==f0) {
    return false;
  }

  res = new FormulaUnit(f, new Inference1(Inference::FORMULA_SHARING, unit), unit->inputType());

  if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] aig_sharing: sharing introduced in " << (*res) << std::endl;
    if (f0->toString()!=f->toString())
      env.out() <<"sharing transformed " << (*unit) << " into " << (*res) << std::endl;
    env.endOutput();
  }

  return true;
}

AIGFormulaSharer::ARes AIGFormulaSharer::getSharedFormula(Formula* f)
{
  CALL("AIGFormulaSharer::getSharedFormula");

  ARes res;

  if(_formAIGs.find(f,res.second)) {
    res.first = aigToFormula(res.second);
    return res;
  }

  switch (f->connective()) {
  case TRUE:
  case FALSE:
    res = applyTrueFalse(f);
    break;
  case LITERAL:
    res = applyLiteral(f);
    break;
  case AND:
  case OR:
    res = applyJunction(f);
    break;
  case NOT:
    res = applyNot(f);
    break;
  case IMP:
  case IFF:
  case XOR:
    res = applyBinary(f);
    break;
  case FORALL:
  case EXISTS:
    res = applyQuantified(f);
    break;
  case ITE:
    res = applyIte(f);
    break;

  case TERM_LET:
  case FORMULA_LET:
  default:
    ASSERTION_VIOLATION;
  }

  if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] aig_subformula_nodes: SFN: "<< (*f) 
            << " has AIG node " << res.second.toString() << std::endl;
    env.endOutput();
  }

  res.first = SimplifyFalseTrue::simplify(res.first);

  res = ARes(shareFormula(res.first,res.second), res.second);

  return res;
}

AIGFormulaSharer::ARes AIGFormulaSharer::apply(Formula* f)
{
  CALL("AIGFormulaSharer::apply(Formula*)");

  ARes res = getSharedFormula(f);

  if(res.first!=f) {
    _formAIGs.insert(f, res.second);
  }

  if(_useRewrites) {
    AIGRef rewriteSrc = res.second;
    AIGRef rewriteTgt = _transf.lev0Deref(rewriteSrc, _rewrites);
    if(rewriteSrc!=rewriteTgt) {
      Formula* formTgt = aigToFormula(rewriteTgt);
      res = ARes(formTgt, rewriteTgt);
    }
  }

  return res;
}

AIGFormulaSharer::ARes AIGFormulaSharer::applyTrueFalse(Formula* f)
{
  CALL("AIGFormulaSharer::applyTrueFalse");

  AIGRef ar = (f->connective()==TRUE) ? _aig.getTrue() : _aig.getFalse();
  return ARes(f, ar);
}

AIGFormulaSharer::ARes AIGFormulaSharer::applyLiteral(Formula* f)
{
  CALL("AIGFormulaSharer::applyLiteral");

  AIGRef ar = apply(f->literal());
  return ARes(f, ar);
}

AIGFormulaSharer::ARes AIGFormulaSharer::applyJunction(Formula* f)
{
  CALL("AIGFormulaSharer::applyJunction");

  bool modified = false;
  Stack<AIGRef> aigs;
  aigs.reset();
  Stack<Formula*> newForms;
  newForms.reset();

  if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] aig_junction_building: building junction " << (*f) << std::endl;
    env.endOutput();
  }

  FormulaList::Iterator fit(f->args());
  while(fit.hasNext()) {
    Formula* f0 = fit.next();
    ARes ar = apply(f0);
    newForms.push(ar.first);
    aigs.push(ar.second);
    if (env.options->showPreprocessing()) {
      env.beginOutput();
      env.out() << "[PP] aig_junction_building: obtained AIG " << ar.second.toString()
              << " for " << (*f0) << std::endl;
      env.endOutput();
    }
    modified |= f0!=ar.first;
  }

  //normalize the order of aigs before joining them together
  sort(aigs.begin(), aigs.end());

  bool conj = f->connective()==AND;
  AIGRef ar;
  if(aigs.isEmpty()) {
    ar = conj ? _aig.getTrue() : _aig.getFalse();
  }
  else {
    ar = aigs.pop();
    if (env.options->showPreprocessing()) {
      env.beginOutput();
      env.out() << "[PP] aig_junction_building: initial conj AIG " 
              << ar.toString() << std::endl;
      env.endOutput();
    }    
    while(aigs.isNonEmpty()) {
      AIGRef cur = aigs.pop();
      if (env.options->showPreprocessing()) {
        env.beginOutput();
        env.out() << "[PP] aig_junction_building: added AIG " << cur.toString() << std::endl;
        env.endOutput();
      }
      if(conj) {
        ar = _aig.getConj(ar, cur);
      }
      else {
        ar = _aig.getDisj(ar, cur);
      }
    }
  }
  if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] aig_junction_building: final AIG " << ar.toString() << std::endl;
    env.endOutput();
  }

  Formula* f1;
  if(modified) {
    FormulaList* forms = 0;
    FormulaList::pushFromIterator(Stack<Formula*>::Iterator(newForms), forms);
    f1 = new JunctionFormula(f->connective(), forms);
  }
  else {
    f1 = f;
  }

  return ARes(f1, ar);
}

AIGFormulaSharer::ARes AIGFormulaSharer::applyNot(Formula* f)
{
  CALL("AIGFormulaSharer::applyNot");

  ARes chRes = apply(f->uarg());
  AIGRef ar = chRes.second.neg();
  Formula* f1 = (f->uarg()==chRes.first) ? f : new NegatedFormula(chRes.first);
  return ARes(f1, ar);
}

AIGFormulaSharer::ARes AIGFormulaSharer::applyBinary(Formula* f)
{
  CALL("AIGFormulaSharer::applyImp");

  ARes lhsRes = apply(f->left());
  ARes rhsRes = apply(f->right());

  AIGRef ar;
  switch(f->connective()) {
  case IFF:
    // (~l \/ r) /\ (l \/ ~r) ---> ~(l /\ ~r) /\ ~(~l /\ r)
    ar = _aig.getConj(_aig.getConj(lhsRes.second, rhsRes.second.neg()).neg(),
		      _aig.getConj(lhsRes.second.neg(), rhsRes.second).neg());
    break;
  case XOR:
    // (~l /\ r) \/ (l /\ ~r) ---> ~(~(l /\ ~r) /\ ~(~l /\ r))
    ar = _aig.getConj(_aig.getConj(lhsRes.second, rhsRes.second.neg()).neg(),
		      _aig.getConj(lhsRes.second.neg(), rhsRes.second).neg()).neg();
    break;
  case IMP:
    // ~l \/ r ---> ~(l /\ ~r)
    ar = _aig.getConj(lhsRes.second, rhsRes.second.neg()).neg();
    break;
  default:
    ASSERTION_VIOLATION;
  }

  bool modified = (f->left() != lhsRes.first) || (f->right() != rhsRes.first);
  Formula* f1 = modified ? new BinaryFormula(f->connective(), lhsRes.first, rhsRes.first) : f;
  return ARes(f1, ar);
}

AIGFormulaSharer::ARes AIGFormulaSharer::applyQuantified(Formula* f)
{
  CALL("AIGFormulaSharer::applyQuantified");

  Connective con = f->connective();
  ARes chRes = apply(f->qarg());
  AIGRef ar = _aig.getQuant(con==EXISTS, f->vars()->copy(), chRes.second);
  Formula* f1 = (f->qarg()==chRes.first) ? f : new QuantifiedFormula(con, f->vars(), chRes.first);
  return ARes(f1, ar);
}

AIGFormulaSharer::ARes AIGFormulaSharer::applyIte(Formula* f)
{
  CALL("AIGFormulaSharer::applyIte");
  ASS_EQ(f->connective(),ITE);

  ARes cond = apply(f->condArg());
  ARes thenBranch = apply(f->thenArg());
  ARes elseBranch = apply(f->elseArg());
  // (~cond \/ then) /\ (cond \/ else)
  AIGRef resAig = _aig.getConj(_aig.getDisj(cond.second.neg(), thenBranch.second), _aig.getDisj(cond.second, elseBranch.second));
  Formula* resForm;
  if(cond.first==f->condArg() && thenBranch.first==f->thenArg() && elseBranch.first==f->elseArg()) {
    resForm = f;
  }
  else {
    resForm = new IteFormula(cond.first, thenBranch.first, elseBranch.first);
  }
  return ARes(resForm, resAig);
}

AIGRef AIGFormulaSharer::getAIG(Clause* cl)
{
  CALL("AIGFormulaSharer::getAIG");

  AIGRef res = _aig.getFalse();
  Clause::Iterator cit(*cl);
  while(cit.hasNext()) {
    Literal* l = cit.next();
    res = _aig.getDisj(res, apply(l));
  }
  res = _aig.getQuant(false, res.getFreeVars(), res);
  return res;
}

/**
 * Rewrite corresponding srcs into corresponding tgts.
 *
 * The function can be called only once on an AIGFormulaSharer object,
 * before we start applying it to any formulas.
 *
 * If rewrites are cyclic or there are multiple definitions for one AIG,
 * some rewrites will be left out.
 *
 * @param usedIdxAcc if non-zero, will receive indexes of rewrites that
 * 	  are being used. The indexes will be in topological order.
 * @param cnt ???
 * @param srcs ???
 * @param tgts ???
 */
void AIGFormulaSharer::addRewriteRules(unsigned cnt, Formula* const * srcs, Formula* const * tgts,
				       Stack<unsigned>* usedIdxAcc)
{
  CALL("AIGFormulaSharer::addRewriteRule");
  ASS(_rewrites.isEmpty());
  ASS(_formReprs.isEmpty());

  if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] aig_rwr: adding "<<cnt<<" AIG-based rewrite rules" << std::endl;
    env.endOutput();
  }

  DHMap<AIGRef,unsigned> refIndexes;
  for(unsigned i=0; i<cnt; ++i) {
    AIGRef src = apply(srcs[i]).second;
    AIGRef tgt = apply(tgts[i]).second;
    if(!src.polarity()) {
      src = src.neg();
      tgt = tgt.neg();
    }
    if(!_rewrites.insert(src, tgt)) {
      continue;
    }
    ALWAYS(refIndexes.insert(src, i));
  }

  Stack<AIGRef> refOrder;
  _transf.saturateMap(_rewrites, &refOrder);

//  _transf.restrictToGetOrderedDomain(_rewrites, refOrder);
  _formReprs.reset();

  _useRewrites = true;

  Stack<AIGRef>::BottomFirstIterator orefIt(refOrder);
  while(orefIt.hasNext()) {
    AIGRef r = orefIt.next();
    unsigned idx = refIndexes.get(r);
    if(_preBuildRewriteCache) {
      //We put the target formula for idx-th rewrite into the _formReprs cache.
      //The call to restrictToGetOrderedDomain() ensures we do apply the targets
      //in the right order to inline rewrites into each orther when needed.
      if (env.options->showPreprocessing()) {
        env.beginOutput();
        env.out() << "[PP] aig_rwr: building rewriting cache for "<<(*srcs[idx])
                <<" by rewriting "<<(*tgts[idx]) << std::endl;
      }
      ARes applyRes = apply(tgts[idx]);
      if (env.options->showPreprocessing()) {
        env.out() << "[PP] aig_rwr: result: "<<applyRes.second
                <<" --> "<<(*applyRes.first) << std::endl;
        env.endOutput();
      }
    }
    if(usedIdxAcc) {
      usedIdxAcc->push(idx);
    }
  }
}

}
