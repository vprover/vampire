/**
 * @file AIG.cpp
 * Implements class AIG.
 */

#include "Lib/Allocator.hpp"
#include "Lib/Metaiterators.hpp"

#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Term.hpp"

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
    /** Universa quantifier */
    QUANT
  };

  CLASS_NAME("AIG::Node");
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
      VarList* _qVars;
    };
  };

public:
  Node(unsigned nodeIdx, Kind k) : _kind(k), _nodeIdx(nodeIdx) {
    ASS_NEQ(k,ATOM);
    if(k==QUANT) {
      _qVars = 0;
    }
  }
  Node(unsigned nodeIdx, Literal* atm) : _kind(ATOM), _nodeIdx(nodeIdx), _lit(atm) { ASS(atm->isPositive()); }

  ~Node() {
    if(kind()==QUANT) {
      _qVars->destroy();
    }
  }

  Kind kind() const { return _kind; }
  /**
   * Index of the node which is unique among nodes with
   * the same parent AIG object.
   *
   * We assign indexes to nodes so we can deterministically normalize
   * node order in conjunction nodes
   */
  unsigned nodeIdx() const { return _nodeIdx; }
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
  VarList* qVars() const {
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
  void setQuantArgs(VarList* vars, Ref par)
  {
    ASS_EQ(kind(), QUANT);
    if(_qVars) {
      _qVars->destroy();
    }
    _qVars = vars;
    _qPar = par;
  }
};

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
    return Hash::combine(3, Hash::combine(p1, p2));
  }
  case Node::QUANT:
  {
    unsigned res = n->qParent().hash();
    VarList::Iterator vit(n->qVars());
    while(vit.hasNext()) {
      res = Hash::combine(res, vit.next());
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
    if(n1->qParent()!=n2->qParent()) { return false; }
    return iteratorsEqual(VarList::Iterator(n1->qVars()), VarList::Iterator(n2->qVars()));
  default:
    ASSERTION_VIOLATION;
  }
}


bool AIG::Ref::isPropConst() const
{
  return node()->kind()==Node::TRUE_CONST;
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
    return n1<n2;
  }
  if(polarity() && !r.polarity()) {
    return true;
  }
  return false;
}

AIG::AIG() : _simplLevel(2), _nextNodeIdx(0), _conjReserve(0), _quantReserve(0)
{
  CALL("AIG::AIG");
  _trueNode = new Node(_nextNodeIdx++, Node::TRUE_CONST);
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
  res = new Node(_nextNodeIdx++, positiveLiteral);
  _atomNodes.insert(positiveLiteral, res);
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
    _conjReserve = new Node(_nextNodeIdx++, Node::CONJ);
  }
  normalizeRefOrder(par1,par2);
  _conjReserve->setConjParents(par1,par2);
  Node* res = _compNodes.insert(_conjReserve);
  if(res==_conjReserve) {
    //we have used the reserve
    _conjReserve = 0;
  }
  return res;
}

AIG::Node* AIG::univQuantNode(VarList* vars, Ref par)
{
  CALL("AIG::univQuantNode");

  if(vars->length()>1) {
    static Stack<int> varStack;
    varStack.reset();
    varStack.loadFromIterator(VarList::DestructiveIterator(vars));
    sort(varStack.begin(), varStack.end());
    vars = 0;
    VarList::pushFromIterator(Stack<int>::Iterator(varStack), vars);
  }

  if(!_quantReserve) {
    _quantReserve = new Node(_nextNodeIdx++, Node::QUANT);
  }
  _quantReserve->setQuantArgs(vars, par);
  Node* res = _compNodes.insert(_conjReserve);
  if(res==_quantReserve) {
    //we have used the reserve
    _quantReserve = 0;
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

  Ref res;
  if(!tryConjSimpl(par1, par2, res)) {
    res = Ref(conjNode(par1, par2), true);
  }
  return res;
}

AIG::Ref AIG::getQuant(bool exQuant, VarList* vars, Ref par)
{
  CALL("AIG::getQuant");

  if(exQuant) {
    return Ref(univQuantNode(vars, par.neg()), false);
  }
  else {
    return Ref(univQuantNode(vars, par), true);
  }
}

bool AIG::tryConjSimpl(Ref par1, Ref par2, Ref& res)
{
  CALL("AIG::tryConjSimpl");
  if(_simplLevel<1) { return false; }
  if(tryO1ConjSimpl(par1, par2, res)) { return true; }
  if(_simplLevel<2) { return false; }
  if(tryO2ConjSimpl(par1, par2, res)) { return true; }
  if(_simplLevel<3) { return false; }
  if(tryO3ConjSimpl(par1, par2, res)) { return true; }
  if(_simplLevel<4) { return false; }
  return tryO4ConjSimpl(par1, par2, res);
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
  if(tryO2AsymetricConjSimpl(par2, par1, res)) { return true; }
  return false;
}
bool AIG::tryO2AsymetricConjSimpl(Ref par1, Ref par2, Ref& res)
{
  CALL("AIG::tryO2ConjSimpl");

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
  if(pn1->kind()!=Node::CONJ) { return false; }
  Ref gp21 = pn2->parent(0);
  Ref gp22 = pn2->parent(1);

  if(!par1.polarity()) {
    if(par2.polarity()) {
      if(gp11.neg()==gp21 || gp11.neg()==gp22 || gp12.neg()==gp21 || gp12.neg()==gp22) {
	res = par2; // ~(a /\ b) /\ (c /\ d) [a!=c | a!=d | b!=c | b!=d] ---> c
	return true;
      }
    }
    else {
//      if(gp11.neg()==gp21 || gp11.neg()==gp22 || gp12.neg()==gp21 || gp12.neg()==gp22) {
//	res = par2; // ~(a /\ b) /\ (c /\ d) [a!=c | a!=d | b!=c | b!=d] ---> c
//	return true;
//      }
    }
  }
  return false;
  NOT_IMPLEMENTED;
}
bool AIG::tryO3ConjSimpl(Ref par1, Ref par2, Ref& res)
{
  CALL("AIG::tryO3ConjSimpl");
  NOT_IMPLEMENTED;
}
bool AIG::tryO4ConjSimpl(Ref par1, Ref par2, Ref& res)
{
  CALL("AIG::tryO4ConjSimpl");
  NOT_IMPLEMENTED;
}

///////////////////////
// AIGFormulaSharer
//

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
  Formula* res;
  if(_formReprs.find(aig, res)) {
    return res;
  }
  _formReprs.insert(aig, f);
  return f;
}

bool AIGFormulaSharer::apply(FormulaUnit* unit, FormulaUnit*& res)
{
  CALL("AIGFormulaSharer::apply(Unit*,Unit*&)");

  Formula* f0 = unit->formula();
  Formula* f = apply(f0).first;

  if(f==f0) {
    return false;
  }

  res = new FormulaUnit(f, new Inference1(Inference::FORMULA_SHARING, unit), unit->inputType());

  TRACE("pp_aig",
      string s0 = f0->toString();
      string s1 = f->toString();
      if(s0==s1) {
	tout << "sharing introduced in " << (*res) << endl;
      }
      else {
	tout << "sharing transformed " << (*unit) << " into " << (*res) << endl;
      }
  );

  return true;
}


AIGFormulaSharer::ARes AIGFormulaSharer::apply(Formula* f)
{
  CALL("AIGFormulaSharer::apply(Formula*)");
  switch (f->connective()) {
  case TRUE:
  case FALSE:
    return applyTrueFalse(f);
  case LITERAL:
    return applyLiteral(f);
  case AND:
  case OR:
    return applyJunction(f);
  case NOT:
    return applyNot(f);
  case IMP:
  case IFF:
  case XOR:
    return applyBinary(f);
  case FORALL:
  case EXISTS:
    return applyQuantified(f);

  case ITE:
  case TERM_LET:
  case FORMULA_LET:
  default:
    ASSERTION_VIOLATION;
  }
}

AIGFormulaSharer::ARes AIGFormulaSharer::applyTrueFalse(Formula* f)
{
  CALL("AIGFormulaSharer::applyTrueFalse");

  AIGRef ar = (f->connective()==TRUE) ? _aig.getTrue() : _aig.getFalse();
  return ARes(shareFormula(f, ar), ar);
}

AIGFormulaSharer::ARes AIGFormulaSharer::applyLiteral(Formula* f)
{
  CALL("AIGFormulaSharer::applyLiteral");

  AIGRef ar = _aig.getLit(f->literal());
  return ARes(shareFormula(f, ar), ar);
}

AIGFormulaSharer::ARes AIGFormulaSharer::applyJunction(Formula* f)
{
  CALL("AIGFormulaSharer::applyJunction");

  bool modified = false;
  static Stack<AIGRef> aigs;
  aigs.reset();
  static Stack<Formula*> newForms;
  newForms.reset();

  FormulaList::Iterator fit(f->args());
  while(fit.hasNext()) {
    Formula* f0 = fit.next();
    ARes ar = apply(f0);
    newForms.push(ar.first);
    aigs.push(ar.second);
    modified |= f0!=ar.first;
  }

  //normalize the order of aigs before joining them together
  sort(aigs.begin(), aigs.end());

  bool conj = f->connective()==AND;
  AIGRef ar = conj ? _aig.getTrue() : _aig.getFalse();
  while(aigs.isNonEmpty()) {
    AIGRef cur = aigs.pop();
    if(conj) {
      ar = _aig.getConj(ar, cur);
    }
    else {
      ar = _aig.getDisj(ar, cur);
    }
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

  return ARes(shareFormula(f1, ar), ar);
}

AIGFormulaSharer::ARes AIGFormulaSharer::applyNot(Formula* f)
{
  CALL("AIGFormulaSharer::applyNot");

  ARes chRes = apply(f->uarg());
  AIGRef ar = chRes.second.neg();
  Formula* f1 = (f->uarg()==chRes.first) ? f : new NegatedFormula(chRes.first);
  return ARes(shareFormula(f1, ar), ar);
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
  return ARes(shareFormula(f1, ar), ar);
}

AIGFormulaSharer::ARes AIGFormulaSharer::applyQuantified(Formula* f)
{
  CALL("AIGFormulaSharer::applyQuantified");

  Connective con = f->connective();
  ARes chRes = apply(f->qarg());
  AIGRef ar = _aig.getQuant(con==EXISTS, f->vars()->copy(), chRes.second);
  Formula* f1 = (f->qarg()==chRes.first) ? f : new QuantifiedFormula(con, f->vars(), chRes.first);
  return ARes(shareFormula(f1, ar), ar);
}




}
