/**
 * @file AIG.cpp
 * Implements class AIG.
 */

#include <algorithm>
#include <sstream>

#include "Lib/Allocator.hpp"
#include "Lib/Metaiterators.hpp"

#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Term.hpp"

#include "PDInliner.hpp"
#include "PDUtils.hpp"

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
    VarList::Iterator vit(node()->qVars());
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

AIG::AIG() : _simplLevel(3), _nextNodeIdx(0), _conjReserve(0), _quantReserve(0)
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
  ASS(vars);

  if(vars->length()>1) {
    static Stack<int> varStack;
    varStack.reset();
    varStack.loadFromIterator(VarList::DestructiveIterator(vars));
    std::sort(varStack.begin(), varStack.end());
    vars = 0;
    VarList::pushFromIterator(Stack<int>::Iterator(varStack), vars);
  }

  if(!_quantReserve) {
    _quantReserve = new Node(_nextNodeIdx++, Node::QUANT);
  }
  _quantReserve->setQuantArgs(vars, par);
  Node* res = _compNodes.insert(_quantReserve);
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

AIG::Ref AIG::getQuant(bool exQuant, VarList* vars, Ref par)
{
  CALL("AIG::getQuant");

  if(!vars) { return par; }

  if(exQuant) {
    return Ref(univQuantNode(vars, par.neg()), false);
  }
  else {
    return Ref(univQuantNode(vars, par), true);
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
  ARes ar = apply(f0);
  Formula* f = ar.first;

  LOG("pp_aig_nodes", (*unit) << " has AIG node " << ar.second.toString());

  if(f==f0) {
    return false;
  }

  res = new FormulaUnit(f, new Inference1(Inference::FORMULA_SHARING, unit), unit->inputType());

  LOG("pp_aig_sharing", "sharing introduced in " << (*res));
  COND_LOG("pp_aig_transf", f0->toString()!=f->toString(),
      "sharing transformed " << (*unit) << " into " << (*res));

  return true;
}


AIGFormulaSharer::ARes AIGFormulaSharer::apply(Formula* f)
{
  CALL("AIGFormulaSharer::apply(Formula*)");

  ARes res;
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
  case TERM_LET:
  case FORMULA_LET:
  default:
    ASSERTION_VIOLATION;
  }

  LOG("pp_aig_subformula_nodes", "SFN: "<< (*f) << " has AIG node " << res.second.toString());

  return res;
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
  Stack<AIGRef> aigs;
  aigs.reset();
  Stack<Formula*> newForms;
  newForms.reset();

  LOG("pp_aig_junction_building", "building junction " << (*f));

  FormulaList::Iterator fit(f->args());
  while(fit.hasNext()) {
    Formula* f0 = fit.next();
    ARes ar = apply(f0);
    newForms.push(ar.first);
    aigs.push(ar.second);
    LOG("pp_aig_junction_building", "obtained AIG " << ar.second.toString() << " for " << (*f0));
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
    LOG("pp_aig_junction_building", "initial conj AIG " << ar.toString());
    while(aigs.isNonEmpty()) {
      AIGRef cur = aigs.pop();
      LOG("pp_aig_junction_building", "added AIG " << cur.toString());
      if(conj) {
        ar = _aig.getConj(ar, cur);
      }
      else {
        ar = _aig.getDisj(ar, cur);
      }
    }
  }
  LOG("pp_aig_junction_building", "final AIG " << ar.toString());

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


#if 0

////////////////////////
// AIGDefinitionMerger
//

void AIGDefinitionMerger::apply(Problem& prb)
{
  CALL("AIGDefinitionMerger::apply(Problem&)");
  if(apply(prb.units())) {
    prb.invalidateByRemoval();
  }
}

bool AIGDefinitionMerger::apply(UnitList*& units)
{
  CALL("AIGDefinitionMerger::apply(UnitList*&)");

  UnitList* eqs = 0;
  DHSet<Unit*> redundant;
  bool modified = PDInliner(false).apply(units, true);

  discoverEquivalences(units, eqs, redundant);
  if(!eqs) {
    return modified;
  }

  UnitList::DelIterator uit(units);

  units = UnitList::concat(eqs,units);
  while(uit.hasNext()) {
    Unit* u = uit.next();
    if(redundant.contains(u)) {
      uit.del();
    }
  }

  ALWAYS(PDInliner(false).apply(units, true));
  return true;
}

/**
 * Return list of newly discovered equivalences.
 * @c units must not contain any predicate equivalences.
 */
void AIGDefinitionMerger::discoverEquivalences(UnitList* units, UnitList*& eqs, DHSet<Unit*>& redundant)
{
  CALL("AIGDefinitionMerger::discoverEquivalences");

  UnitList* res = 0;

  typedef Stack<FormulaUnit*> FUStack;

  FUStack defs;

  UnitList::Iterator uit(units);
  while(uit.hasNext()) {
    Unit* u = uit.next();
    if(u->isClause()) { continue; }
    FormulaUnit* fu = static_cast<FormulaUnit*>(u);
    ASS(!PDUtils::isPredicateEquivalence(fu));

    if(PDUtils::hasDefinitionShape(fu)) {
      defs.push(fu);
    }
  }

  AIGFormulaSharer _aig;
  DHMap<Formula*,FormulaUnit*> body2def; //maps shared body to a definitions

  UnitList* pendingEquivs = 0;


  FUStack::Iterator fit(defs);
  while(fit.hasNext()) {
    FormulaUnit* fu = fit.next();

    Literal* lhs;
    Formula* rhs;
    PDUtils::splitDefinition(fu, lhs, rhs);
    Formula* shRhs = _aig.apply(rhs).first;

    if(body2def.find(shRhs)) {
      FormulaUnit* fu2 = body2def.get(shRhs);
      Literal* lhs2;
      Formula* rhs2;
      PDUtils::splitDefinition(fu2, lhs2, rhs2);

      Formula* equivForm = new BinaryFormula(IFF,
	  new AtomicFormula(lhs), new AtomicFormula(lhs2));
      Inference* inf = new Inference2(Inference::PREDICATE_DEFINITION_MERGING, fu, fu2);
      FormulaUnit* equivFU = new FormulaUnit(equivForm, inf, Unit::getInputType(fu->inputType(), fu2->inputType()));

      UnitList::push(equivFU, eqs);
      UnitList::push(equivFU, pendingEquivs);
    }
  }

  typedef pair<Literal*,Literal*> RwrPair;
  Stack<RwrPair> pendingRewrites;

}
#endif
}
