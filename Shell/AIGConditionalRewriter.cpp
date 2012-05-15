/**
 * @file AIGConditionalRewriter.cpp
 * Implements class AIGConditionalRewriter.
 */

#include <algorithm>

#include "Lib/SafeRecursion.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/SubstHelper.hpp"

#include "AIGCompressor.hpp"
#include "AIGSubst.hpp"
#include "Flattening.hpp"

#include "AIGConditionalRewriter.hpp"

namespace Shell
{

/////////////////////////
// AIGPrenexTransformer
//

/**
 * Return the inner AIG of @c a after skipping outer quantifiers.
 */
AIGRef AIGPrenexTransformer::getInner(AIGRef a)
{
  CALL("AIGPrenexTransformer::getInner");

  while(a.isQuantifier()) {
    a = a.parent(0);
  }
  return a;
}

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

  a = getInner(a);
  return !containsQuant(a);
}

void AIGPrenexTransformer::swapPolarity(QIStack& quants)
{
  CALL("AIGPrenexTransformer::swapPolarity");

  size_t cnt = quants.size();
  for(unsigned i=0; i<cnt; i++) {
    quants[i].univ = !quants[i].univ;
  }
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

  //this makes sure that variables in qs are unique
  DEBUG_CODE(
      DHSet<unsigned> vars;
      vars.loadFromIterator(getMappingIteratorKnownRes<unsigned>(QIStack::ConstIterator(qs), QuantInfo::getVar));
      ASS_EQ(vars.size(), qs.size());
      );

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

#if OLD_PRENEX

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

#else

struct AIGPrenexTransformer::QuantUnifierN
{
public:
  QuantUnifierN(AIG& aig, AIG::VarSet* freeVars, size_t aigCnt, QuantAIG* aigs)
   : _aig(aig), _nextAvailVar(0), _rnm(aigCnt), _aigCnt(aigCnt), _aigs(aigs)
  {
    CALL("AIGPrenexTransformer::QuantUnifier::QuantUnifier");

    LOG("pp_aig_pren_qu", "QuantUnifier init, freeVars: "<<freeVars->toString()<<" aigCnt: "<<aigCnt);
    TRACE("pp_aig_pren_qu_args", tout << "  quantifier blocks:" <<endl;
	for(size_t i=0; i<aigCnt; i++) {
	  tout << "  aig "<<i<<":" <<endl;
	  QIStack::BottomFirstIterator qit(aigs[i].second);
	  while(qit.hasNext()) {
	    QuantInfo qi = qit.next();
	    tout << "    "<<(qi.univ ? "un " : "ex ")<<qi.var<<endl;
	  }
	}
    );


    _usedVars.loadFromIterator(AIG::VarSet::Iterator(*freeVars));
    process();
  }


  AIGStack getResultingInnerAigs() const { return _ares; }
  const QIStack& getResQuantInfo() const { return _qres; }

private:

  void addExQuantifier(QuantInfo q, size_t aigIdx)
  {
    CALL("addExQuantifier");
    ASS(!q.univ);

    unsigned tgtVar = q.var;
    if(!_usedVars.insert(tgtVar)) {
      tgtVar = getNextFreshVar();
    }
    LOG("pp_aig_pren_qu","added exQuant for aig "<<aigIdx<<" locVar: "<< q.var <<" globVar: "<<tgtVar);
    if(tgtVar!=q.var) {
      ALWAYS(_rnm[aigIdx].insert(q.var, TermList(tgtVar, false)));
    }
    _qres.push(QuantInfo(tgtVar, false));
  }

  void addUnivQuantifier(const QIStack& aigQuants, const Stack<size_t>& aigIndexes)
  {
    CALL("addExQuantifier");
    ASS_EQ(aigQuants.size(), aigIndexes.size());
    ASS(aigQuants.isNonEmpty());

    unsigned tgtVar = aigQuants.top().var;
    if(!_usedVars.insert(tgtVar)) {
      tgtVar = getNextFreshVar();
    }

    LOG("pp_aig_pren_qu","added univQuant, globVar: "<<tgtVar);
    size_t cnt = aigQuants.size();
    for(size_t i=0; i<cnt; i++) {
      ASS(aigQuants[i].univ);
      unsigned locVar = aigQuants[i].var;
      LOG("pp_aig_pren_qu","  in aig "<<aigIndexes[i]<<" locVar: "<< locVar);
      if(tgtVar!=locVar) {
	size_t locIdx = aigIndexes[i];
        ALWAYS(_rnm[locIdx].insert(locVar, TermList(tgtVar, false)));
      }
    }
    _qres.push(QuantInfo(tgtVar, true));
  }

  void process()
  {
    CALL("AIGPrenexTransformer::QuantUnifier::process");

    DArray<size_t> qIndexes;
    qIndexes.init(_aigCnt, 0);
    Stack<size_t> liveAigIndexes;
    liveAigIndexes.loadFromIterator(getRangeIterator(static_cast<size_t>(0), _aigCnt));

    for(;;) {
      Stack<size_t>::DelIterator laiIt(liveAigIndexes);
      while(laiIt.hasNext()) {
	size_t aIdx = laiIt.next();
	QIStack& quants = _aigs[aIdx].second;
	size_t& qIdx = qIndexes[aIdx];
	while(qIdx<quants.size() && !quants[qIdx].univ) {
	  LOG("pp_aig_pren_qu","ex aIdx: "<<aIdx<<" var: "<<quants[qIdx].var<<" qIdx: "<< qIdx);
	  addExQuantifier(quants[qIdx], aIdx);
	  qIdx++;
	}
	if(qIdx>=quants.size()) {
	  laiIt.del();
	}
      }

      if(liveAigIndexes.isEmpty()) {
	break;
      }
      //here all alive have one universal quantifier in front

      static QIStack univQuants;
      univQuants.reset();

      Stack<size_t>::BottomFirstIterator laiUnivIt(liveAigIndexes);
      while(laiUnivIt.hasNext()) {
	size_t aIdx = laiUnivIt.next();
	QIStack& quants = _aigs[aIdx].second;
	size_t& qIdx = qIndexes[aIdx];
	ASS_L(qIdx,quants.size());
	ASS(quants[qIdx].univ);

	LOG("pp_aig_pren_qu","un aIdx: "<<aIdx<<" var: "<<quants[qIdx].var<<" qIdx: "<< qIdx);
	univQuants.push(quants[qIdx]);
	qIdx++;
      }

      ASS_EQ(univQuants.size(), liveAigIndexes.size());
      addUnivQuantifier(univQuants, liveAigIndexes);
    }

    sortQuantSegments(_qres);

    for(size_t idx=0; idx<_aigCnt; idx++) {
      AIGRef renAig;
      if(_rnm[idx].isEmpty()) {
	renAig = _aigs[idx].first;
      }
      else {
	renAig = AIGSubst(_aig).apply(SubstHelper::getMapApplicator(&_rnm[idx]), _aigs[idx].first);
      }
      _ares.push(renAig);

    }
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

  AIG& _aig;

  DHSet<unsigned> _usedVars;
  unsigned _nextAvailVar;

  DArray<DHMap<unsigned,TermList> > _rnm;

  size_t _aigCnt;
  QuantAIG* _aigs;

  AIGStack _ares;
  QIStack _qres;
};


/**
 * Visitor for use in the SafeRecursion object
 */
struct AIGPrenexTransformer::RecursiveVisitor
{
  RecursiveVisitor(AIGPrenexTransformer& parent)
      : _parent(parent), _aig(parent._aig) {}

  template<class ChildCallback>
  void pre(AIGRef obj, ChildCallback fn)
  {
    CALL("AIGPrenexTransformer::RecursiveVisitor::pre");

    if(obj.isAtom() || obj.isPropConst()) {
      return;
    }
    if(_transfCache.find(obj.getPositive())) {
      return;
    }

    if(obj.isQuantifier()) {
      fn(getInner(obj));
      return;
    }
    ASS_REP(obj.isConjunction(), obj);
    static AIGStack conjuncts;
    conjuncts.reset();
    _aig.collectConjuncts(obj.getPositive(), conjuncts);
    while(conjuncts.isNonEmpty()) {
      fn(conjuncts.pop());
    }
  }

  QuantAIG post(AIGRef obj, size_t childCnt, QuantAIG* childRes)
  {
    CALL("AIGPrenexTransformer::RecursiveVisitor::post");

    if(obj.isAtom() || obj.isPropConst()) {
      ASS_EQ(childCnt,0);
      return QuantAIG(obj,QIStack());
    }
    AIGRef objPos = obj.getPositive();
    QuantAIG posRes;
    bool cached = false;
    if(_transfCache.find(obj.getPositive(), posRes)) {
      cached = true;
    }
    else if(objPos.isQuantifier()) {
      ASS_EQ(childCnt,1);
      QuantAIG& child = childRes[0];
      posRes.first = child.first;
      AIGRef aux;
      collectQuants(objPos, posRes.second, aux);
      posRes.second.loadFromIterator(QIStack::BottomFirstIterator(child.second));
    }
    else {
      ASS(objPos.isConjunction());

      QuantUnifierN qu(_aig, objPos.getFreeVars(), childCnt, childRes);
      posRes.first =_aig.makeConjunction(qu.getResultingInnerAigs());
      posRes.second = qu.getResQuantInfo();

      LOG("pp_aig_pren_conj_res", "conj prenex transform:"<<endl<<
          "  src: "<<objPos<<endl<<
          "  tgt: "<<_parent.quantifyBySpec(posRes.second, posRes.first));
    }

    if(!cached) {
      ALWAYS(_transfCache.insert(objPos, posRes));
    }

    QuantAIG res(posRes);
    if(!obj.polarity()) {
      res.first = res.first.neg();
      swapPolarity(res.second);
    }
    return res;
  }

  AIGPrenexTransformer& _parent;
  AIG& _aig;
  DHMap<AIGRef,QuantAIG> _transfCache;
};

#endif


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


AIGRef AIGPrenexTransformer::apply(AIGRef a0)
{
  CALL("AIGPrenexTransformer::apply");

#if OLD_PRENEX
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
#else
  RecursiveVisitor visitor(*this);
  SafeRecursion<AIGRef, QuantAIG, RecursiveVisitor> srec(visitor);
  QuantAIG resQ = srec(a0);

  AIGRef res = quantifyBySpec(resQ.second, resQ.first);

  return res;
#endif
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

//////////////////////////////
// AIGFactorizingTransformer
//

struct AIGFactorizingTransformer::LocalFactorizer
{
  LocalFactorizer(AIGFactorizingTransformer& parent) : _parent(parent), _aig(parent._aig) {}

  static AIGRef getSiblingDisjunct(AIGRef disjunction, AIGRef oneChild)
  {
    CALL("AIGFactorizingTransformer::LocalFactorizer::getSiblingDisjunct");
    ASS(disjunction.isConjunction());
    ASS(!disjunction.polarity());
    if(disjunction.parent(0).neg()==oneChild) {
      return disjunction.parent(1).neg();
    }
    ASS_EQ(disjunction.parent(1).neg(),oneChild);
    return disjunction.parent(0).neg();
  }

  AIGRef getFactoredDisjunctionAndUpdateOccData(AIGRef factoredChild, const AIGStack& disjunctionStack)
  {
    CALL("AIGFactorizingTransformer::LocalFactorizer::getFactoredDisjunctionAndUpdateOccData");

    static AIGStack conjuncts;
    conjuncts.reset();
    AIGStack::ConstIterator dit(disjunctionStack);
    while(dit.hasNext()) {
      AIGRef disj = dit.next();
      AIGRef conjunct = getSiblingDisjunct(disj, factoredChild);
      conjuncts.push(conjunct);

      AIGStack& updatedOccStack = _occMap.get(conjunct);
      ASS_NEQ(&updatedOccStack, &disjunctionStack);
      updatedOccStack.remove(disj);  //can cause quadratic behavior
      if(updatedOccStack.size()<2) {
	_subAigs.remove(conjunct);   //can cause quadratic behavior
      }
    }
    AIGRef subConj = _aig.makeConjunction(conjuncts);
    AIGRef res = _aig.getDisj(factoredChild, subConj);
    return res;
  }

  void apply(AIGStack& conjs)
  {
    CALL("AIGFactorizingTransformer::LocalFactorizer::apply");

    LOG("pp_aig_fact_lcl_steps","local factorization call started");

    _subAigs.reset();
    _occMap.reset();

    size_t conjCnt0 = conjs.size();
    makeUnique(conjs);
    COND_LOG("pp_aig_fact_lcl_steps",conjCnt0!=conjs.size(),
	"removed duplicate conjuncts, cnt0="<<conjCnt0<<" cnt="<<conjs.size());
    scan(conjs);

    static DHSet<AIGRef> removedConjs;
    removedConjs.reset();

    while(_subAigs.isNonEmpty()) {
      AIGRef fdisj = getMostFactorableDisjunct();

      AIGStack& occStack= _occMap.get(fdisj);
      ASS_GE(occStack.size(),2);

      AIGRef mergedDisj = getFactoredDisjunctionAndUpdateOccData(fdisj, occStack);
      TRACE("pp_aig_fact_lcl_steps",
	  tout<<"local factorization step:"<<endl<<
	    "  disjunct: "<<fdisj<<endl<<
	    "  merged:   "<<mergedDisj<<endl;
	  AIGStack::ConstIterator rmIt(occStack);
	  while(rmIt.hasNext()) {
	    tout << "  removed:  " << rmIt.next()<<endl;
	  }
      );
      DEBUG_CODE(
	  AIGStack::ConstIterator rmIt(occStack);
	  while(rmIt.hasNext()) {
	    AIGRef removed = rmIt.next();
	    ASS_NEQ(removed, mergedDisj);
	  }
	);

      removedConjs.loadFromIterator(AIGStack::ConstIterator(occStack));
      conjs.push(mergedDisj);
      occStack.reset();
      ALWAYS(_subAigs.remove(fdisj));   //can cause quadratic behavior
    }

    AIGStack::DelIterator cleaningIt(conjs);
    while(cleaningIt.hasNext()) {
      AIGRef a = cleaningIt.next();
      if(removedConjs.contains(a)) {
	cleaningIt.del();
      }
    }
    LOG("pp_aig_fact_lcl_steps","local factorization call finished");
  }

private:

  void scanOccurrence(AIGRef conjunct, AIGRef subDisjunct)
  {
    CALL("AIGFactorizingTransformer::LocalFactorizer::scanOccurrence");

    AIGStack* occStackPtr;
    _occMap.getValuePtr(subDisjunct, occStackPtr, AIGStack());
    occStackPtr->push(conjunct);
    if(occStackPtr->size()==2) {
      _subAigs.push(subDisjunct);
    }
  }

  void scan(const AIGStack& conjs)
  {
    CALL("AIGFactorizingTransformer::LocalFactorizer::scan");

    AIGStack::ConstIterator scanIt(conjs);
    while(scanIt.hasNext()) {
      AIGRef a = scanIt.next();
      if(!a.isConjunction()) {
        continue;
      }
      ASS(!a.polarity()); //positive conjunctions were split by AIG::collectConjuncts

      scanOccurrence(a, a.parent(0).neg());
      scanOccurrence(a, a.parent(1).neg());
    }
  }

  AIGRef getMostFactorableDisjunct()
  {
    CALL("AIGFactorizingTransformer::LocalFactorizer::getMostFactorableDisjunct");
    ASS(_subAigs.isNonEmpty());

    unsigned mostOcc = 0;
    AIGRef res;

    AIGStack::ConstIterator sit(_subAigs);
    while(sit.hasNext()) {
      AIGRef sAig = sit.next();
      unsigned occCnt = _occMap.get(sAig).size();
      if(occCnt>mostOcc) {
	mostOcc = occCnt;
	res = sAig;
      }
    }
    ASS_GE(mostOcc, 2);
    return res;
  }

  /** sub-disjuncts which can be potentially factored out (i.e. occur in at least two conjuncts) */
  AIGStack _subAigs;
  /**
   * Map of sub-disjuncts to conjuncts in which they occur
   */
  DHMap<AIGRef,AIGStack> _occMap;

  AIGFactorizingTransformer& _parent;
  AIG& _aig;
};

void AIGFactorizingTransformer::doLocalFactorization(AIGStack& conj)
{
  CALL("AIGFactorizingTransformer::doLocalFactorization");

  LocalFactorizer fact(*this);
  fact.apply(conj);
}

/**
 * Visitor for use in the SafeRecursion object
 */
struct AIGFactorizingTransformer::RecursiveVisitor
{
  RecursiveVisitor(AIGFactorizingTransformer& parent)
      : _parent(parent), _aig(parent._aig), _transfCache(parent._transfCache) {}

  template<class ChildCallback>
  void pre(AIGRef obj, ChildCallback fn)
  {
    CALL("AIGFactorizingTransformer::RecursiveVisitor::pre");

    if(obj.isAtom() || obj.isPropConst()) {
      return;
    }
    if(_transfCache.find(obj.getPositive())) {
      return;
    }

    if(obj.isQuantifier()) {
      fn(obj.parent(0));
      return;
    }
    ASS_REP(obj.isConjunction(), obj);
    static AIGStack conjuncts;
    conjuncts.reset();
    _aig.collectConjuncts(obj.getPositive(), conjuncts);
    while(conjuncts.isNonEmpty()) {
      fn(conjuncts.pop());
    }
  }

  AIGRef post(AIGRef obj, size_t childCnt, AIGRef* childRes)
  {
    CALL("AIGFactorizingTransformer::RecursiveVisitor::post");

    if(obj.isAtom() || obj.isPropConst()) {
      ASS_EQ(childCnt,0);
      return obj;
    }
    AIGRef res;
    if(_transfCache.find(obj.getPositive(), res)) {
      ASS_EQ(childCnt,0);
      return AIGTransformer::lev0Deref(obj, _transfCache);
    }

    AIGRef posRes;
    if(obj.isQuantifier()) {
      ASS_EQ(childCnt,1);
      if(childRes[0]==obj.parent(0)) {
	return obj;
      }
      posRes = _aig.getQuant(false, obj.getQuantifierVars(), childRes[0]);
    }
    else {
      ASS(obj.isConjunction());

      static AIGStack childNodes;
      childNodes.reset();
      childNodes.loadFromIterator(getArrayishObjectIterator(childRes, childCnt));
      _aig.flattenConjuncts(childNodes);
      _parent.doLocalFactorization(childNodes);
      posRes = _aig.makeConjunction(childNodes);

      COND_LOG("pp_aig_fact_conj_transf", obj.getPositive()!=posRes, "factor transf:"<<endl<<
	  "  src: "<<obj.getPositive()<<endl<<
	  "  tgt: "<<posRes);
    }

    ALWAYS(_transfCache.insert(obj.getPositive(), posRes));
    return obj.polarity() ? posRes : posRes.neg();
  }

  AIGFactorizingTransformer& _parent;
  AIG& _aig;
  RefMap& _transfCache;
};

AIGRef AIGFactorizingTransformer::apply(AIGRef a0)
{
  CALL("AIGFactorizingTransformer::apply");

  RecursiveVisitor visitor(*this);
  SafeRecursion<AIGRef,AIGRef,RecursiveVisitor> safeRec(visitor);
  return safeRec(a0);
}


///////////////////////////
// AIGConditionalRewriter
//

AIGConditionalRewriter::AIGConditionalRewriter()
 : _aig(_afs.aig())
{
  CALL("AIGConditionalRewriter::AIGConditionalRewriter");

  _engine = new AIGInliningEngine(_aig);
}

void AIGConditionalRewriter::apply(Problem& prb)
{
  CALL("AIGConditionalRewriter::apply(Problem&)");

  apply(prb.units());
  prb.invalidateEverything();
}

void AIGConditionalRewriter::apply(UnitList*& units)
{
  CALL("AIGConditionalRewriter::apply(UnitList*&)");

  AIGRef conj = _aig.getTrue();
  UnitStack leftAside;

  UnitList::Iterator uit(units);
  while(uit.hasNext()) {
    Unit* u = uit.next();
    if(u->inputType()!=Unit::AXIOM) {
      leftAside.push(u);
      continue;
    }
    LOG_UNIT("pp_aig_cr_inp", u);
    AIGRef unitAig;
    if(u->isClause()) {
      Clause* cl = static_cast<Clause*>(u);
      unitAig = _afs.getAIG(cl);
    }
    else {
      FormulaUnit* fu = static_cast<FormulaUnit*>(u);
      unitAig = _afs.apply(fu->formula()).second;
    }
    conj = _aig.getConj(conj, unitAig);
  }

  AIGRef conjTransf = apply(conj);

  Formula* baseForm = _afs.aigToFormula(conjTransf);
  FormulaUnit* fu = new FormulaUnit(baseForm, new Inference(Inference::LOCAL_SIMPLIFICATION), Unit::AXIOM);
  fu = Flattening::flatten(fu);
  units->destroy();
  units = 0;
  UnitList::pushFromIterator(UnitStack::Iterator(leftAside), units);
  UnitList::push(fu, units);

  TopLevelFlatten().apply(units);

  TRACE("pp_aig_cr_out",
      UnitList::Iterator uit(units);
      while(uit.hasNext()) {
	Unit* u = uit.next();
	TRACE_OUTPUT_UNIT(u);
      }
      );
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

AIGRef AIGConditionalRewriter::applyInner(AIGRef a0)
{
  CALL("AIGConditionalRewriter::applyInner");

  AIGStack premises;
  AIGRef a = _engine->apply(a0, &premises);
//  AIGRef a = a0;
  COND_TRACE("pp_aig_cr_engine_step", a!=a0,
      tout << "pp_aig_cr_engine_step"<<endl;
      tout << "  src: "<<a0<<endl;
      tout << "  tgt: "<<a<<endl;
      AIGStack::ConstIterator pit(premises);
      while(pit.hasNext()) {
	tout << "  prem: " << pit.next() << endl;
      }
      );

  if(!a.isConjunction()) {
    return a;
  }

  AIGStack conjs;
  _aig.collectConjuncts(a, conjs);

  if(conjs.size()>2) {
    //we want to merge equivalences expressed as two conjuncts into a single disjunction.
    //This however makes sense only if there is more conjuncts than just the two
    //(in this case we'd also get an infinite recursion...)
    EquivStack eqs;
    collectEquivs(conjs, eqs);
    while(eqs.isNonEmpty()) {
      Equiv eq = eqs.pop();
      LOG("pp_aig_cr_equiv", "pp_aig_cr_equiv: "<< eq.toString());
      conjs.push(eq.getDisjunctiveRepr(_aig));
    }
  }


  AIGStack::ConstIterator citPre(conjs);
  while(citPre.hasNext()) {
    AIGRef cur = citPre.next();
    _engine->addValidNode(cur);
  }


  AIGStack::DelIterator citInner(conjs);
  while(citInner.hasNext()) {
    AIGRef cur = citInner.next();
    _engine->removeValidNode(cur);

    AIGRef curProcessed;
    if(cur.isConjunction()) {
      ASS(!cur.polarity());
      curProcessed = applyInner(cur.neg()).neg();
    }
    else {
      curProcessed = applyInner(cur);
    }

    ASS(!cur.isConjunction() || !cur.polarity());

    if(curProcessed!=cur) {
      citInner.replace(curProcessed);
    }

    _engine->addValidNode(curProcessed);
  }

  AIGStack::ConstIterator citPost(conjs);
  while(citPost.hasNext()) {
    AIGRef cur = citPost.next();
    _engine->removeValidNode(cur);
  }

  AIGRef res = _aig.makeConjunction(conjs);

  COND_LOG("pp_aig_cr_inner_step", a0!=res,
	 "pp_aig_cr_inner_step"<<endl
      << "  src: "<<a0<<endl
      << "  tgt: "<<res);

  return res;
}

AIGRef AIGConditionalRewriter::apply(AIGRef a0)
{
  CALL("AIGConditionalRewriter::apply");

  _freshnessGuard.use();

  AIGRef outer = a0;

  AIGPrenexTransformer apt(_aig);
  outer = apt.apply(outer);

  AIGFactorizingTransformer factor(_aig);
  outer = factor.apply(outer);

  AIGRef inner;
  apt.collectQuants(outer, _prenexQuantifiers, inner);

  AIGCompressor acr(_aig);
  AIGRef prev;
  do {
    prev = inner;
    inner = applyInner(inner);
    inner = acr.compress(inner);
  } while(prev!=inner);

  outer = apt.quantifyBySpec(_prenexQuantifiers, inner);

  AIGMiniscopingTransformer minis(_aig);
  outer = minis.apply(outer);

  return outer;


//  LOG("bug","init:  "<<a0);
//  LOG("bug","pren: "<<aPrenex);
//  LOG("bug","fact: "<<aFactor);
//  LOG("bug","mnsc: "<<aMinis);
//  LOG("bug","-----------------------");
//  LOG("bug","-----------------------");
//  LOG("bug","-----------------------");
//
//  AIGStack conjs;
//  _aig.collectConjuncts(factInner, conjs);
//
//  EquivStack eqs;
//  collectEquivs(conjs, eqs);
//
//  LOGV("bug",conjs.size());
//
//  AIGCompressor aCompr(_aig);
//
//  while(conjs.isNonEmpty()) {
//    AIGRef conjunct = conjs.pop();
//    AIGRef conjSimp = aCompr.compress(conjunct);
//    LOGV("bug", conjunct);
//    if(conjunct!=conjSimp) {
//      LOGV("bug", conjSimp);
//    }
//  }
//
//  while(eqs.isNonEmpty()) {
//    LOGV("bug", eqs.pop().toString());
//  }
//
////  LOG("bug","-----------------------");
////  LOG("bug","-----------------------");
////  LOG("bug","-----------------------");
////
////  _aig.collectConjuncts(aMinis, conjs);
////  LOGV("bug",conjs.size());
////
////  while(conjs.isNonEmpty()) {
////    LOGV("bug", conjs.pop());
////  }
//
//  return aPrenex;
}


}
