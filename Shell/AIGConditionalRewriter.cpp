/**
 * @file AIGConditionalRewriter.cpp
 * Implements class AIGConditionalRewriter.
 */

#include <algorithm>

#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/SubstHelper.hpp"

#include "AIGSubst.hpp"

#include "AIGConditionalRewriter.hpp"

namespace Shell
{

/////////////////////////
// AIGPrenexTransformer
//

bool AIGPrenexTransformer::containsQuant(AIGRef a0)
{
  CALL("AIGPrenexTransformer::containsQuant");

  static AIGInsideOutPosIterator ait;
  ait.reset(a0);
  while(ait.hasNext()) {
    AIGRef a = ait.next();
    if(a.isQuantifier()) {
      return true;
    }
  }
  return false;
}

bool AIGPrenexTransformer::isPrenex(AIGRef a)
{
  CALL("AIGPrenexTransformer::isPrenex");

  while(a.isQuantifier()) {
    a = a.parent(0);
  }
  return !containsQuant(a);
}

/**
 * Ensure that variables in segments of @c qs with the same quantifier
 * are sorted in ascending order.
 *
 * The implementation assumes that the segments usually are already sorted.
 */
void AIGPrenexTransformer::sortQuantSegments(QIStack& qs)
{
  CALL("AIGPrenexTransformer::sortQuantSegments");

  QuantInfo* qiArr = qs.begin();

  unsigned sz = qs.size();
  unsigned segStart = 0;
  bool segUnsorted = false;
  for(unsigned i=1; i<sz; i++) {
    if(qs[i-1].univ==qs[i].univ) {
      //we're staying in the same segment
      if(qs[i-1].var>qs[i].var) {
	segUnsorted = true;
      }
      continue;
    }
    if(segUnsorted) {
      std::sort(qiArr+segStart, qiArr+i, QuantInfo::compareVars);
    }
    segStart = i;
    segUnsorted = false;
  }
}

/**
 * Collect quantifiers from @c a which must be in prenex form.
 * Outer quantifiers go in the stack @c quants at the bottom.
 */
void AIGPrenexTransformer::collectQuants(AIGRef a, QIStack& quants, AIGRef& inner)
{
  CALL("AIGPrenexTransformer::collectQuants");
  ASS(quants.isEmpty());

  bool pol = true;
  while(a.isQuantifier()) {
    if(!a.polarity()) {
      pol = !pol;
    }
    AIG::VarSet::Iterator vit(*a.getQuantifierVars());
    while(vit.hasNext()) {
      unsigned var = vit.next();
      quants.push(QuantInfo(var, pol));
    }
    a = a.parent(0);
  }
  if(!pol) {
    a = a.neg();
  }
  inner = a;


  //The requirement on QIStack is that variables in a block
  //of quantifiers of the same kind are sorted.
  //Even though the variables we get from VarSet::Iterator are in
  //ascending order, we still need to check sortedness to handle
  //the case with two nested quantifier nodes of the same kind.

  sortQuantSegments(quants);
}


struct AIGPrenexTransformer::QuantUnifier
{
public:
  QuantUnifier(AIG& aig, AIG::VarSet* freeVars, AIGRef a1, const QIStack& q1, AIGRef a2, const QIStack& q2)
   : _nextAvailVar(0),
     _aig(aig), _a1(a1), _q1(q1), _a2(a2), _q2(q2)
  {
    CALL("AIGPrenexTransformer::QuantUnifier::QuantUnifier");

    LOG("pp_aig_pren_qu", "QuantUnifier init");

    _usedVars.loadFromIterator(AIG::VarSet::Iterator(*freeVars));

    process();
  }


  AIGRef getResultingInnerAig1() const { return _a1res; }
  AIGRef getResultingInnerAig2() const { return _a2res; }
  const QIStack& getResQuantInfo() const { return _qres; }

private:

  void addResultingQuantifier(QuantInfo q1, QuantInfo q2)
  {
    CALL("AIGPrenexTransformer::QuantUnifier::getResult");
    ASS(q1.isValid() || q2.isValid());
    ASS(!q1.isValid() || !q2.isValid() || q1.univ==q2.univ);

    bool univ = q1.isValid() ? q1.univ : q2.univ;
    unsigned tgtVar = q1.isValid() ? q1.var : q2.var;
    if(!_usedVars.insert(tgtVar)) {
      tgtVar = getNextFreshVar();
    }

    if(q1.isValid() && tgtVar!=q1.var) {
      ALWAYS(_rnm1.insert(q1.var, TermList(tgtVar, false)));
      LOG("pp_aig_pren_qu", "adding rewrite to 1: "<< q1.var << " --> "<<tgtVar);
    }
    if(q2.isValid() && tgtVar!=q2.var) {
      ALWAYS(_rnm2.insert(q2.var, TermList(tgtVar, false)));
      LOG("pp_aig_pren_qu", "adding rewrite to 2: "<< q2.var << " --> "<<tgtVar);
    }

    _qres.push(QuantInfo(tgtVar, univ));
  }


  void process()
  {
    CALL("AIGPrenexTransformer::QuantUnifier::process");

    unsigned qidx1 = 0;
    unsigned qidx2 = 0;

    //we merge universal quantifiers and transfer the existential without merging
    while(qidx1<_q1.size() && qidx2<_q2.size()) {
      while(qidx1<_q1.size() && qidx2<_q2.size() && _q1[qidx1].univ && _q2[qidx2].univ) {
	addResultingQuantifier(_q1[qidx1],_q2[qidx2]);
	qidx1++; qidx2++;
      }
      while(qidx1<_q1.size() && !_q1[qidx1].univ) {
	addResultingQuantifier(_q1[qidx1],QuantInfo());
	qidx1++;
      }
      while(qidx2<_q2.size() && !_q2[qidx2].univ) {
	addResultingQuantifier(QuantInfo(),_q2[qidx2]);
	qidx2++;
      }
    }
    //when there is nothing left to merge, we just transfer the remaining quantifiers
    while(qidx1<_q1.size()) {
      addResultingQuantifier(_q1[qidx1],QuantInfo());
      qidx1++;
    }
    while(qidx2<_q2.size()) {
      addResultingQuantifier(QuantInfo(),_q2[qidx2]);
      qidx2++;
    }

    sortQuantSegments(_qres);

    _a1res = AIGSubst(_aig).apply(SubstHelper::getMapApplicator(&_rnm1), _a1);
    _a2res = AIGSubst(_aig).apply(SubstHelper::getMapApplicator(&_rnm2), _a2);
  }


  unsigned getNextFreshVar()
  {
    CALL("AIGPrenexTransformer::QuantUnifier::getNextFreshVar");

    while(_usedVars.find(_nextAvailVar)) {
      _nextAvailVar++;
    }
    unsigned res = _nextAvailVar++;
    ALWAYS(_usedVars.insert(res));
    return res;
  }

  DHSet<unsigned> _usedVars;
  unsigned _nextAvailVar;

  DHMap<unsigned,TermList> _rnm1;
  DHMap<unsigned,TermList> _rnm2;

  AIG& _aig;
  AIG::VarSet* _freeVars;
  AIGRef _a1;
  const QIStack& _q1;
  AIGRef _a2;
  const QIStack& _q2;
  AIGRef _a1res;
  AIGRef _a2res;
  QIStack _qres;
};


/**
 *
 * @param freeVars is union of free variables of a1 and a2 after
 *        quantification, and these should not be renamed
 */
void AIGPrenexTransformer::unifyQuants(AIG::VarSet* freeVars, AIGRef a1, const QIStack& q1, AIGRef a2, const QIStack& q2,
      AIGRef& a1res, AIGRef& a2res, QIStack& qres)
{
  CALL("AIGPrenexTransformer::unifyQuants");

  QuantUnifier qu(_aig, freeVars, a1, q1, a2, q2);

  a1res = qu.getResultingInnerAig1();
  a2res = qu.getResultingInnerAig2();
  qres = qu.getResQuantInfo();
}

AIGRef AIGPrenexTransformer::quantifyBySpec(const QIStack& qs, AIGRef inner)
{
  CALL("AIGPrenexTransformer::quantifyBySpec");

  if(qs.isEmpty()) {
    return inner;
  }

  static Stack<unsigned> currVars;
  currVars.reset();
  bool currIsUniv = qs.top().univ; //actualy the initial value doesn't matter

  QIStack::TopFirstIterator qit(qs);
  while(qit.hasNext()) {
    QuantInfo qi = qit.next();
    if(qi.univ!=currIsUniv) {
      ASS(currVars.isNonEmpty());
      AIG::VarSet* varSet = AIG::VarSet::getFromArray(currVars.begin(), currVars.size());
      inner = _aig.getQuant(!currIsUniv, varSet, inner);
      currVars.reset();
      currIsUniv = qi.univ;
    }
    currVars.push(qi.var);
  }
  AIG::VarSet* varSet = AIG::VarSet::getFromArray(currVars.begin(), currVars.size());
  inner = _aig.getQuant(!currIsUniv, varSet, inner);

  return inner;
}

AIGRef AIGPrenexTransformer::processConjunction(AIGRef a)
{
  CALL("AIGPrenexTransformer::processConjunction");
  ASS(a.isConjunction());
  ASS_EQ(a.parentCnt(),2);

  AIGRef p1 = _atr.lev0Deref(a.parent(0), _transfCache);
  AIGRef p2 = _atr.lev0Deref(a.parent(1), _transfCache);

  static QIStack p1Quants;
  static QIStack p2Quants;
  p1Quants.reset();
  p2Quants.reset();

  AIGRef inner1;
  AIGRef inner2;

  collectQuants(p1, p1Quants, inner1);
  collectQuants(p2, p2Quants, inner2);

  if(p1Quants.isEmpty() && p2Quants.isEmpty()) {
    return a;
  }

  static QIStack unifQuants;
  unifQuants.reset();

  AIGRef inner1Transf;
  AIGRef inner2Transf;
  unifyQuants(a.getFreeVars(), inner1, p1Quants, inner2, p2Quants, inner1Transf, inner2Transf, unifQuants);

  AIGRef resConj = _aig.getConj(inner1Transf, inner2Transf);

  AIGRef res = quantifyBySpec(unifQuants, resConj);

  LOG("pp_aig_pren_conj_res", "conj prenex transform:"<<endl<<
      "  src: "<<a<<endl<<
      "  tgt: "<<res);

  return res;
}

AIGRef AIGPrenexTransformer::apply(AIGRef a0)
{
  CALL("AIGPrenexTransformer::apply");

  _buildingIterator.addToTraversal(a0);

  while(_buildingIterator.hasNext()) {
    AIGRef src = _buildingIterator.next();
    AIGRef tgt;
    if(src.isAtom() || src.isPropConst()) {
      tgt = src;
    }
    else if(src.isQuantifier()) {
      tgt = _atr.lev1Deref(src, _transfCache);
    }
    else {
      ASS(src.isConjunction());
      tgt = processConjunction(src);
    }
    if(src!=tgt) {
      _transfCache.insert(src, tgt);
    }
  }

  AIGRef res = _atr.lev0Deref(a0, _transfCache);

  ASS_REP2(isPrenex(res), a0, res);

  return res;
}

//////////////////////////////
// AIGMiniscopingTransformer
//

AIGRef AIGMiniscopingTransformer::processQuantifier(AIGRef a)
{
  CALL("AIGMiniscopingTransformer::processQuantifier");
  ASS(a.polarity());
  ASS(a.isQuantifier());

  AIGRef qarg = a.parent(0);
  AIG::VarSet* qargVars = a.getQuantifierVars();

  AIGRef res;
  if(qarg.isConjunction()) {
    AIGRef carg1 =qarg.parent(0);
    AIGRef carg2 =qarg.parent(1);
    if(qarg.polarity()) {
      //we have ![X]: (A & B) which we can simplify to (![X]: A) & (![X]: B)

      //AIG::getQuant takes care of removing vars which don't occur in the quantifier body as free
      AIGRef qcarg1 = _aig.getQuant(false, qargVars, carg1);
      AIGRef qcarg2 = _aig.getQuant(false, qargVars, carg2);

      res = _aig.getConj(qcarg1, qcarg2);
    }
    else {
      //we have ![X,X1,X2]: (A[X,X1] | B[X,X2]) which we can simplify to ![X]: ((![X1]: A) | (![X2]: B))
      AIG::VarSet* a1qvars = qargVars->getIntersection(carg1.getFreeVars());
      AIG::VarSet* a2qvars = qargVars->getIntersection(carg2.getFreeVars());
      ASS(a1qvars->getUnion(a2qvars)==qargVars);
      if(a1qvars!=a2qvars) {
	AIG::VarSet* intersVars = a1qvars->getIntersection(a2qvars);
	AIG::VarSet* a1only = a1qvars->subtract(intersVars);
	AIG::VarSet* a2only = a2qvars->subtract(intersVars);

	AIGRef qcarg1 = _aig.getQuant(false, a1only, carg1.neg());
	AIGRef qcarg2 = _aig.getQuant(false, a2only, carg2.neg());
	AIGRef conj = _aig.getConj(qcarg1.neg(), qcarg2.neg());

	res = _aig.getQuant(false, intersVars, conj.neg());
      }
      else {
	//we cannot do anything here
	res = a;
      }
    }
  }
  else {
    res = a;
  }
  COND_LOG("pp_aig_minis_step", res!=a,"miniscoping step:"<<endl<<
      "  src: "<<a<<endl<<
      "  tgt: "<<res);
  return res;
}

AIGRef AIGMiniscopingTransformer::apply(AIGRef a0)
{
  CALL("AIGMiniscopingTransformer::apply");

  _buildingIterator.addToTraversal(a0);

  while(_buildingIterator.hasNext()) {
    AIGRef src = _buildingIterator.next();
    AIGRef tgt;
    if(src.isAtom() || src.isPropConst()) {
      tgt = src;
    }
    else if(src.isConjunction()) {
      tgt = _atr.lev1Deref(src, _transfCache);
    }
    else {
      ASS(src.isQuantifier());
      ASS(src.polarity()); //this follows from the behavior of AIGInsideOutPosIterator
      tgt = _atr.lev1Deref(src, _transfCache);
      tgt = processQuantifier(tgt);

      _buildingIterator.addToTraversal(tgt);
    }
    if(src!=tgt) {
      _transfCache.insert(src, tgt);
    }
  }

  AIGRef res = _atr.lev0Deref(a0, _transfCache);

  return res;
}


///////////////////////////
// AIGConditionalRewriter
//

AIGConditionalRewriter::AIGConditionalRewriter()
 : _aig(_afs.aig())
{
  CALL("AIGConditionalRewriter::AIGConditionalRewriter");
}

void AIGConditionalRewriter::apply(Problem& prb)
{
  CALL("AIGConditionalRewriter::apply(Problem&)");

  apply(prb.units());
}

void AIGConditionalRewriter::apply(UnitList*& units)
{
  CALL("AIGConditionalRewriter::apply(UnitList*&)");

  AIGRef conj = _aig.getTrue();

  UnitList::Iterator uit(units);
  while(uit.hasNext()) {
    Unit* u = uit.next();
    if(u->isClause()) { continue; }
    FormulaUnit* fu = static_cast<FormulaUnit*>(u);
    AIGRef unitAig = _afs.apply(fu->formula()).second;
    conj = _aig.getConj(conj, unitAig);
  }

  AIGRef conjTransf = apply(conj);
}

void AIGConditionalRewriter::collectConjuncts(AIGRef aig, AIGStack& res)
{
  CALL("AIGConditionalRewriter::collectConjuncts");
  ASS(res.isEmpty());

  static AIGStack toDo;
  toDo.reset();
  toDo.push(aig);
  while(toDo.isNonEmpty()) {
    AIGRef a = toDo.pop();
    if(!a.polarity() || !a.isConjunction()) {
      res.push(a);
      continue;
    }
    toDo.push(a.parent(0));
    toDo.push(a.parent(1));
  }
}

/**
 * Check for equivalence in the form
 * (a /\ b) \/ (~a /\ ~b)
 * in the term of AIGs written as ~and(~and(a,b),~and(~a,~b)).
 * They are called disjunction equivalences, as they have disjunction
 * at the top level.
 */
bool AIGConditionalRewriter::isDisjEquiv(AIGRef a, Equiv& eq)
{
  CALL("AIGConditionalRewriter::isDisjEquiv");

  if(!a.isConjunction() || a.polarity()) { return false; }

  AIGRef p1 = a.parent(0);
  AIGRef p2 = a.parent(1);
  if(p1.polarity() || p2.polarity() || !p1.isConjunction() || !p2.isConjunction()) { return false; }

  if( (p1.parent(0)==p2.parent(0).neg() && p1.parent(1)==p2.parent(1).neg()) ||
      (p1.parent(0)==p2.parent(1).neg() && p1.parent(1)==p2.parent(0).neg()) ) {
    eq.first = p1.parent(0);
    eq.second = p1.parent(1);

    if(!eq.first.polarity()) {
      eq.first = eq.first.neg();
      eq.second = eq.second.neg();
    }
    return true;
  }
  return false;
}

AIGRef AIGConditionalRewriter::getOppositeImpl(AIGRef a)
{
  CALL("AIGConditionalRewriter::getOppositeImpl");
  ASS(a.isConjunction());
  ASS(!a.polarity());

  return _aig.getConj(a.parent(0).neg(), a.parent(1).neg()).neg();
}

/**
 * Check for equivalence in the form
 * (a \/ ~b) /\ (~a \/ b)
 * in the term of AIGs written as and(~and(~a,b),~and(a,~b)).
 * They are called disjunction equivalences, as they have disjunction
 * at the top level.
 */
void AIGConditionalRewriter::collectConjEquivs(AIGStack& conjStack, EquivStack& res)
{
  CALL("AIGConditionalRewriter::collectConjEquivs");

  //implications present in the conjunction
  static DHSet<AIGRef> impls;
  //implications that are captured by the discovered equivalences
  static DHSet<AIGRef> eqImpls;

  impls.reset();
  eqImpls.reset();

  AIGStack::Iterator implScanIt(conjStack);
  while(implScanIt.hasNext()) {
    AIGRef a = implScanIt.next();
    if(!a.isConjunction()) {
      continue;
    }
    ASS(!a.polarity()); //we're travensing a conjunct stack, so positive conjunctiona have been splitted

    AIGRef aOpp = getOppositeImpl(a);
    if(impls.contains(aOpp)) {
      res.push(Equiv(a.parent(0), a.parent(1).neg()));
      eqImpls.insert(a);
      eqImpls.insert(aOpp);
      continue;
    }

    impls.insert(a);
  }

  AIGStack::DelIterator cleaningIt(conjStack);
  while(cleaningIt.hasNext()) {
    AIGRef a = cleaningIt.next();
    if(eqImpls.contains(a)) {
      cleaningIt.del();
    }
  }
}

void AIGConditionalRewriter::collectEquivs(AIGStack& conjStack, EquivStack& res)
{
  CALL("AIGConditionalRewriter::collectEquivs");

  //first collect disjunction equivalences
  AIGStack::DelIterator dEqColIt(conjStack);
  while(dEqColIt.hasNext()) {
    AIGRef a = dEqColIt.next();
    Equiv eq;
    if(isDisjEquiv(a, eq)) {
      res.push(eq);
      dEqColIt.del();
    }
  }

  //and now conjunction equivalences
  collectConjEquivs(conjStack, res);
}

AIGRef AIGConditionalRewriter::apply(AIGRef a0)
{
  CALL("AIGConditionalRewriter::apply");

  //TODO: finish
  AIGPrenexTransformer apt(_aig);
  AIGRef aPrenex = apt.apply(a0);


  AIGMiniscopingTransformer minis(_aig);
  AIGRef aMinis = minis.apply(aPrenex);

  LOG("bug","init:  "<<a0);
  LOG("bug","pren: "<<aPrenex);
  LOG("bug","mnsc: "<<aMinis);

  AIGPrenexTransformer::QIStack quants;
  AIGRef prenexInner;
  apt.collectQuants(aPrenex, quants, prenexInner);

  LOG("bug","-----------------------");
  LOG("bug","-----------------------");
  LOG("bug","-----------------------");

  AIGStack conjs;
  collectConjuncts(prenexInner, conjs);

  EquivStack eqs;
  collectEquivs(conjs, eqs);

  LOGV("bug",conjs.size());

  while(conjs.isNonEmpty()) {
    LOGV("bug", conjs.pop());
  }

  while(eqs.isNonEmpty()) {
    LOGV("bug", eqs.pop().toString());
  }

  LOG("bug","-----------------------");
  LOG("bug","-----------------------");
  LOG("bug","-----------------------");

  collectConjuncts(aMinis, conjs);
  LOGV("bug",conjs.size());

  while(conjs.isNonEmpty()) {
    LOGV("bug", conjs.pop());
  }

  return aPrenex;
}


}
