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

#include "Shell/Options.hpp"

#include "AIG.hpp"


namespace Shell {

class AIGSubst {
public:
  AIGSubst(AIG& aig) : _aig(aig) {}

  template<class Applicator>
  AIGRef apply(Applicator apl, AIGRef aig);

private:
  typedef const SharedSet<unsigned> VarSet;

  template<class Applicator>
  VarSet* getSubstFreeVars(Applicator apl, AIGRef aig);

  void getQuantVars(AIGRef aig, DHSet<unsigned>& res);
  void buildQuantRenaming(VarSet* substFreeVars, const DHSet<unsigned>& quantVars, DHMap<unsigned,unsigned>& res);

  VarSet* mapVarSet(VarSet* vs, const DHMap<unsigned,unsigned>& map);

#if 0
  template<class Inner>
  struct WrapperSubst
  {
    CLASS_NAME("AIGSubst::WrapperSubst")
    USE_ALLOCATOR(WrapperSubst);

    WrapperSubst(Inner& inner, VarSet* forbidden)
    : _inner(inner), _nextCandidate(0)
    {
      CALL("AIGSubst::WrapperSubst::WrapperSubst");

      _forbidden.loadFromIterator(VarSet::Iterator(*forbidden));
    }

    void enterQuantifier(AIGRef quant)
    {
      CALL("AIGSubst::WrapperSubst::enterQuantifier");

      VarSet* vars = quant.getQuantifierVars();
      VarSet::Iterator vit(*vars);
      while(vit.hasNext()) {
	unsigned var = vit.next();
	if(_renaming.find(var)) {
	  continue;
	}
	unsigned tgt;
	if(_forbidden.find(var)) {
	  while(_forbidden.find(_nextCandidate)) {
	    _nextCandidate++;
	  }
	  tgt = _nextCandidate++;
	}
	else {
	  tgt = var;
	}
	_renaming.insert(var, tgt);
	_forbidden.insert(tgt);
      }
    }
    AIGRef applyToQuantifier(AIGRef quant, AIGRef newBody)
    {

    }

    TermList apply(unsigned var) {
      unsigned renRes;
      if(_renaming.find(var, renRes)) {
	return TermList(renRes, false);
      }
      return _inner.apply(var);
    }

    Inner& _inner;
    DHSet<unsigned> _forbidden;
    /** next candidate for a fresh variable */
    unsigned _nextCandidate;
    DHMap<unsigned,unsigned> _renaming;
  };
#else
  template<class Inner>
  struct FilteringApplicator
  {
    FilteringApplicator(Inner& inner, const DHMap<unsigned,unsigned>& quantMap)
    : _filter(VarSet::getEmpty()), _inner(inner), _quantMap(quantMap) {}

    void setFilter(VarSet* skipped) {
      _filter = skipped;
    }
    TermList apply(unsigned var) {
      if(_filter->member(var)) {
	unsigned res;
	if(!_quantMap.find(var, res)) {
	  res = var;
	}
	return TermList(res, false);
      }
      return _inner.apply(var);
    }

    VarSet* _filter;
    Inner& _inner;
    const DHMap<unsigned,unsigned>& _quantMap;
  };
#endif

  AIG& _aig;
};

/**
 * Return variables that occur in the terms introduced by the substitution.
 * This will be the set of free variables of the result of application of
 * @c apl on @c aig.
 */
template<class Applicator>
AIGSubst::VarSet* AIGSubst::getSubstFreeVars(Applicator apl, AIGRef aig)
{
  CALL("AIGSubst::getSubstFreeVars");

  static Stack<unsigned> varStack;
  varStack.reset();

  VarSet* baseFreeVars = aig.getFreeVars();
  VarSet::Iterator bvit(*baseFreeVars);
  while(bvit.hasNext()) {
    unsigned bv = bvit.next();
    TermList inst = apl.apply(bv);
    if(inst.isVar()) {
      varStack.push(inst.var());
    }
    else {
      varStack.loadFromIterator(VarSet::Iterator(*AIG::getTermFreeVars(inst.term())));
    }
  }

  return VarSet::getFromIterator(Stack<unsigned>::Iterator(varStack));
}

/**
 * Collect variables that occur in quantifiers within @c aig, and add them to @c res.
 */
inline
void AIGSubst::getQuantVars(AIGRef aig, DHSet<unsigned>& res)
{
  CALL("AIGSubst::getQuantVars");

  static AIGInsideOutPosIterator ait;
  ait.reset(aig);
  while(ait.hasNext()) {
    AIGRef a = ait.next();
    if(!a.isQuantifier()) {
      continue;
    }
    res.loadFromIterator(VarSet::Iterator(*a.getQuantifierVars()));
  }
}

/**
 * Create a renaming for @c quantVars so that they do not collide with @c substFreeVars.
 */
inline
void AIGSubst::buildQuantRenaming(VarSet* substFreeVars, const DHSet<unsigned>& quantVars,
    DHMap<unsigned,unsigned>& res)
{
  CALL("AIGSubst::buildQuantRenaming");

  unsigned nextCandidate = 0;
  VarSet::Iterator sfvit(*substFreeVars);
  while(sfvit.hasNext()) {
    unsigned fvar = sfvit.next();
    if(!quantVars.contains(fvar)) {
      continue;
    }
    while(quantVars.contains(nextCandidate) || substFreeVars->member(nextCandidate)) {
      nextCandidate++;
    }
    unsigned tgt = nextCandidate++;
    res.insert(fvar, tgt);
  }
}

/**
 * Transform @c vs using @c map and return the result.
 */
inline
AIGSubst::VarSet* AIGSubst::mapVarSet(VarSet* vs, const DHMap<unsigned,unsigned>& map)
{
  CALL("AIGSubst::mapVarSet");

  static Stack<unsigned> res;
  res.reset();
  VarSet::Iterator vit(*vs);
  while(vit.hasNext()) {
    unsigned var = vit.next();
    map.find(var, var);
    res.push(var);
  }
  VarSet* resSet = VarSet::getFromArray(res.begin(), res.size());
  return resSet;
}

template<class Applicator>
AIGRef AIGSubst::apply(Applicator apl, AIGRef aig)
{
  CALL("AIGSubst::apply");

  VarSet* substFreeVars = getSubstFreeVars(apl, aig);
  static DHSet<unsigned> quantVars;
  quantVars.reset();
  getQuantVars(aig, quantVars);
  static DHMap<unsigned,unsigned> quantMap;
  quantMap.reset();
  buildQuantRenaming(substFreeVars, quantVars, quantMap);

  FilteringApplicator<Applicator> fapl(apl, quantMap);

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
	VarSet* newQVars = mapVarSet(qSet, quantMap);
	if(pparTgt==ppar && newQVars==qSet) {
	  tgt = cAig;
	}
	else {
	  AIGRef parTgt = par.polarity() ? pparTgt : pparTgt.neg();
	  tgt = _aig.getQuant(false, newQVars, parTgt);
	}
	map.insert(curr, tgt);
  if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] aig_subst_quant: quant subst:" << std::endl
            <<"  src: "<<curr.first<<endl
            <<"  tgt: "<<tgt<<endl
            <<"  new quant: "<<newQVars->toString()<<endl;
    env.endOutput();
  }	
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

  if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] aig_subst: aig subst from "<<aig<<" to "<<tgt << std::endl;
    env.endOutput();
  }

  return tgt;
}


}

#endif // __AIGSubst__
