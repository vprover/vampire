/**
 * @file AIGSubst.hpp
 * Defines class AIGSubst.
 */

#ifndef __AIGSubst__
#define __AIGSubst__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/SharedSet.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/SubstHelper.hpp"

#include "AIG.hpp"


namespace Shell {

class AIGSubst {
public:
  AIGSubst(AIG& aig) : _aig(aig) {}

  template<class Applicator>
  AIGRef apply(Applicator apl, AIGRef aig);

private:
  typedef SharedSet<unsigned> VarSet;

  template<class Inner>
  struct FilteringApplicator
  {
    FilteringApplicator(Inner& inner) : _filter(VarSet::getEmpty()), _inner(inner) {}

    void setFilter(VarSet* skipped) {
      _filter = skipped;
    }
    TermList apply(unsigned var) {
      if(_filter->member(var)) {
	return TermList(var, false);
      }
      return _inner.apply(var);
    }

    VarSet* _filter;
    Inner& _inner;
  };

  AIG& _aig;
};


template<class Applicator>
AIGRef AIGSubst::apply(Applicator apl, AIGRef aig)
{
  CALL("AIGSubst::apply");

  FilteringApplicator<Applicator> fapl(apl);

  AIGTransformer atr(_aig);
  typedef pair<AIGRef, VarSet*> QAig;
  static DHMap<QAig, AIGRef> map;
  static Stack<QAig> toDo;

  map.reset();
  toDo.reset();

  QAig topQAig(aig.getPositive(), VarSet::getEmpty());

  toDo.push(topQAig);
  while(toDo.isNonEmpty()) {
    QAig curr = toDo.top();
    if(map.find(curr)) {
      toDo.pop();
      continue;
    }
    AIGRef cAig = curr.first;
    ASS(cAig.polarity());
    if(cAig.isPropConst()) {
      map.insert(curr, cAig);
    }
    else if(cAig.isAtom()) {
      fapl.setFilter(curr.second);
      Literal* substLit = SubstHelper::apply(cAig.getPositiveAtom(), fapl);
      ASS(substLit->isPositive());
      map.insert(curr, _aig.getLit(substLit));
    }
    else if(cAig.isQuantifier()) {
      VarSet* qSet = cAig.getQuantifierVars();
      VarSet* qHistorySet = curr.second->getUnion(qSet);
      AIGRef par = cAig.parent(0);
      AIGRef ppar = par.getPositive();
      QAig qpar = QAig(ppar, qHistorySet);
      AIGRef pparTgt;
      if(map.find(qpar, pparTgt)) {
	AIGRef tgt;
	if(pparTgt==ppar) {
	  tgt = cAig;
	}
	else {
	  AIGRef parTgt = par.polarity() ? pparTgt : pparTgt.neg();
	  tgt = _aig.getQuant(false, cAig.getQuantifierVars(), parTgt);
	}
	map.insert(curr, tgt);
      }
      else {
	toDo.push(qpar);
      }
    }
    else if(cAig.isConjunction()) {
      AIGRef p1 = cAig.parent(0);
      AIGRef p2 = cAig.parent(1);
      AIGRef pp1 = p1.getPositive();
      AIGRef pp2 = p2.getPositive();
      QAig qp1(pp1, curr.second);
      QAig qp2(pp2, curr.second);
      AIGRef pp1Tgt = AIGRef::getInvalid();
      AIGRef pp2Tgt = AIGRef::getInvalid();
      if(!map.find(qp1, pp1Tgt)) {
	toDo.push(qp1);
      }
      if(!map.find(qp2, pp2Tgt)) {
	toDo.push(qp2);
      }
      if(pp1Tgt.isValid() && pp2Tgt.isValid()) {
	AIGRef p1Tgt = p1.polarity() ? pp1Tgt : pp1Tgt.neg();
	AIGRef p2Tgt = p2.polarity() ? pp2Tgt : pp2Tgt.neg();
	AIGRef tgt = _aig.getConj(p1Tgt, p2Tgt);
	map.insert(curr, tgt);
      }
    }
    if(toDo.top()==curr) {
      toDo.pop();
    }
  }

  AIGRef tqTgt = map.get(topQAig);

  AIGRef tgt = aig.polarity() ? tqTgt : tqTgt.neg();

  LOG("pp_aig_subst", "aig subst from "<<aig<<" to "<<tgt);

  return tgt;
}


}

#endif // __AIGSubst__
