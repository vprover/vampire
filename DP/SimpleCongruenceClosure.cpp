/**
 * @file SimpleCongruenceClosure.cpp
 * Implements class SimpleCongruenceClosure.
 */

#include "SimpleCongruenceClosure.hpp"

#include "Lib/Environment.hpp"
#include "Lib/SafeRecursion.hpp"

#include "Kernel/Signature.hpp"

namespace DP
{

const unsigned SimpleCongruenceClosure::NO_SIG_SYMBOL = 0xFFFFFFFF;

SimpleCongruenceClosure::SimpleCongruenceClosure()
{
  CALL("SimpleCongruenceClosure::SimpleCongruenceClosure");

  _cInfos.ensure(1); //this ensures constants will start numbered from 1, not 0

  _posLitConst = getFreshConst();
  _negLitConst = getFreshConst();
  _negEqualities.push(CEq(_posLitConst, _negLitConst, 0));
  LOG("dp_cc_const_intr", "posConst: "<<_posLitConst);
  LOG("dp_cc_const_intr", "negConst: "<<_negLitConst);

//  _unsatEq = CEq(0,0);
}

/** Introduce fresh congruence closure constant */
unsigned SimpleCongruenceClosure::getFreshConst()
{
  CALL("SimpleCongruenceClosure::getFreshConst");

  unsigned res = _cInfos.size();
  _cInfos.expand(res+1);
  _cInfos[res].init();
  return res;
}

/** Get congruence closure constant corresponding to a signature symbol number @c symbol */
unsigned SimpleCongruenceClosure::getSignatureConst(unsigned symbol, bool funct)
{
  CALL("SimpleCongruenceClosure::getSignatureConst");

  unsigned* pRes;
  if(!_sigConsts.getValuePtr(make_pair(symbol, funct), pRes)) {
    return *pRes;
  }
  unsigned res = getFreshConst();
  _cInfos[res].sigSymbol = symbol;
  _cInfos[res].sigSymIsFunct = funct;
  *pRes = res;
  LOG("dp_cc_const_intr", "signConst: "<<res<<" ("
      <<(funct ? env.signature->functionName(symbol) : env.signature->predicateName(symbol) )<<")");

  return res;
}

unsigned SimpleCongruenceClosure::getPairName(CPair p)
{
  CALL("SimpleCongruenceClosure::getPairName");

  unsigned* pRes;
  if(!_pairNames.getValuePtr(p, pRes)) {
    return *pRes;
  }
  unsigned res = getFreshConst();
  _cInfos[res].namedPair = p;
  *pRes = res;

  _cInfos[p.first].useList.push(res);
  _cInfos[p.second].useList.push(res);

  LOG("dp_cc_const_intr", "pairConst: "<<res<<" ("<<p.first<<","<<p.second<<")");
  return res;
}

struct SimpleCongruenceClosure::FOConversionWorker
{
  FOConversionWorker(SimpleCongruenceClosure& parent)
      : _parent(parent) {}


  template<class ChildCallback>
  void pre(TermList t, ChildCallback childCallbackFn) {
    CALL("SimpleCongruenceClosure::FOConversionWorker::pre");

    if(t.isTerm()) {
      if(_parent._termNames.find(t)) {
	//term is in cache, we don't need to traverse it
	return;
      }

      Term::Iterator argIt(t.term());
      while(argIt.hasNext()) {
	TermList arg = argIt.next();
	childCallbackFn(arg);
      }
    }
  }

  unsigned post(TermList t, size_t childCnt, unsigned* childRes)
  {
    CALL("MaxDegreeRetrievalWorker::post");

    unsigned res;
    if(_parent._termNames.find(t, res)) {
      return res;
    }

    if(t.isVar()) {
      ASS_EQ(childCnt,0);
      NOT_IMPLEMENTED;
//      res = _parent.getFreshConst();
    }
    else {
      ASS(t.isTerm());
      Term* trm = t.term();
      res = _parent.getSignatureConst(trm->functor(), true);
      for(size_t i=0; i<childCnt; i++) {
	res = _parent.getPairName(CPair(res, childRes[i]));
      }
    }
    _parent._cInfos[res].term = t;
    _parent._termNames.insert(t, res);
    LOG("dp_cc_fo_conv", "Term "<<t<<" converted to "<<res);
    return res;
  }

  SimpleCongruenceClosure& _parent;
};

unsigned SimpleCongruenceClosure::convertFO(TermList trm)
{
  CALL("SimpleCongruenceClosure::convertFO(TermList)");

  FOConversionWorker wrk(*this);
  SafeRecursion<TermList,unsigned,FOConversionWorker> convertor(wrk);
  return convertor(trm);
}

unsigned SimpleCongruenceClosure::convertFONonEquality(Literal* lit)
{
  CALL("SimpleCongruenceClosure::convertFONonEquality");

  unsigned res = getSignatureConst(lit->functor(), false);
  Term::Iterator ait(lit);
  while(ait.hasNext()) {
    TermList a = ait.next();
    unsigned argConst = convertFO(a);
    res = getPairName(CPair(res, argConst));
  }
  _cInfos[res].lit = lit;

  LOG("dp_cc_fo_conv", "Lit "<<(*Literal::positiveLiteral(lit))<<" converted to "<<res);
  return res;
}

SimpleCongruenceClosure::CEq SimpleCongruenceClosure::convertFOEquality(Literal* equality)
{
  CALL("SimpleCongruenceClosure::convertFOEquality(Literal*)");

  unsigned arg1 = convertFO(*equality->nthArgument(0));
  unsigned arg2 = convertFO(*equality->nthArgument(1));
  return CEq(arg1, arg2, equality);
}

void SimpleCongruenceClosure::addLiterals(LiteralIterator lits)
{
  CALL("SimpleCongruenceClosure::addLiterals");

  while(lits.hasNext()) {
    Literal* l = lits.next();
    if(!l->ground()) {
      //for now we ignore non-ground literals
      LOG("dp_cc_interf_inp", "non-ground lit "<<(*l)<<" skipped");
      continue;
    }
    LOG("dp_cc_interf_inp", "added "<<(*l));
    if(l->isEquality()) {
      CEq eq = convertFOEquality(l);
      if(l->isPositive()) {
	addPendingEquiality(eq);
      }
      else {
	_negEqualities.push(eq);
      }
    }
    else {
      unsigned predConst = convertFONonEquality(l);
      CEq eq;
      if(l->isPositive()) {
	eq = CEq(predConst, _posLitConst, l);
      }
      else {
	eq = CEq(predConst, _negLitConst, l);
      }
      addPendingEquiality(eq);
    }

    _allAddedLits.push(l);
  }
}

void SimpleCongruenceClosure::propagate()
{
  CALL("SimpleCongruenceClosure::propagate");

  while(_pendingEqualities.isNonEmpty()) {
    CEq curr0 = _pendingEqualities.pop();
    CPair curr = deref(curr0);
    if(curr.first==curr.second) {
      continue;
    }
    if(getClassSize(curr.first)>getClassSize(curr.second)) {
      std::swap(curr.first, curr.second);
    }
    unsigned aRep = curr.first;
    unsigned bRep = curr.second;

    ConstInfo& aInfo = _cInfos[aRep];
    ConstInfo& bInfo = _cInfos[bRep];
    ASS_EQ(aInfo.proofPredecessor,0);
    ASS_EQ(aInfo.reprConst,0);
    aInfo.proofPredecessor = bRep;
    aInfo.reprConst = bRep;
    bInfo.classList.push(aRep);
    Stack<unsigned>::Iterator aChildIt(aInfo.classList);
    while(aChildIt.hasNext()) {
      unsigned aChild = aChildIt.next();
      bInfo.classList.push(aChild);
    }
    Stack<unsigned>::Iterator aUseIt(aInfo.useList);
    while(aUseIt.hasNext()) {
      unsigned usePairConst = aUseIt.next();
      CPair usedPair = _cInfos[usePairConst].namedPair;
      ASS(usedPair!=CPair(0,0)); //the constant must be a name of a pair
      CPair derefPair = deref(usedPair);

      unsigned* pDerefPairName;
      if(!_pairNames.getValuePtr(derefPair, pDerefPairName)) {
	addPendingEquiality(CEq(*pDerefPairName, usePairConst));
      }
      else {
	*pDerefPairName = usePairConst;
	bInfo.useList.push(usePairConst);
      }
    }
  }
}

DecisionProcedure::Status SimpleCongruenceClosure::getStatus()
{
  CALL("SimpleCongruenceClosure::getStatus");

  propagate();

  //The intuition is that we want to fail on as early equialities as possible
  //(to improve back-jumping), so we have a BottomUpIterator here.
  //A possible problem with this is that the non-equality true!=false is the
  //first one, so whenever we have a contradiction with non-equality predicates,
  //it will be discovered first.
  Stack<CEq>::BottomFirstIterator neqIt(_negEqualities);
  while(neqIt.hasNext()) {
    CEq neq = neqIt.next();
    CPair derNEq = deref(neq);
    if(derNEq.first==derNEq.second) {
      _unsatEq = neq;
      LOG("dp_cc_contr", "contradiction: ("<<neq.c1<<","<<neq.c2<<") both dereferenced to "<<derNEq.first);
      LOG("dp_cc_interf_res","cc gave UNSAT");
      return DecisionProcedure::UNSATISFIABLE;
    }
  }

  LOG("dp_cc_interf_res","cc gave SAT");
  return DecisionProcedure::SATISFIABLE;
}

void SimpleCongruenceClosure::getUnsatisfiableSubset(LiteralStack& res)
{
  CALL("SimpleCongruenceClosure::getUnsatisfiableSubset");
  ASS(res.isEmpty());
  ASS(!_unsatEq.isInvalid());

  //ineficient but correct: return everything
  res.loadFromIterator(LiteralStack::Iterator(_allAddedLits));
  return;

  static Stack<CEq> toExplain;
  toExplain.push(_unsatEq);



  NOT_IMPLEMENTED;
}


}
