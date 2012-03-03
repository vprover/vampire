/**
 * @file SimpleCongruenceClosure.cpp
 * Implements class SimpleCongruenceClosure.
 */

#include <sstream>

#include "SimpleCongruenceClosure.hpp"

#include "Lib/Environment.hpp"
#include "Lib/IntUnionFind.hpp"
#include "Lib/SafeRecursion.hpp"

#include "Kernel/Signature.hpp"

namespace DP
{

const unsigned SimpleCongruenceClosure::NO_SIG_SYMBOL = 0xFFFFFFFF;

string SimpleCongruenceClosure::CEq::toString() const
{
  CALL("SimpleCongruenceClosure::CEq::toString");

  stringstream res;
  res << c1<<"="<<c2<<" implied by ";
  if(foOrigin) {
    if(foPremise) {
      res << (*foPremise);
    }
    else {
      res << "built-in true!=false";
    }
  }
  else {
    res << "congruence";
  }
  return res.str();
}

string SimpleCongruenceClosure::CEq::toString(SimpleCongruenceClosure& parent) const
{
  CALL("SimpleCongruenceClosure::CEq::toString");

  stringstream res;
  res << c1<<"="<<c2<<" implied by ";
  if(foOrigin) {
    if(foPremise) {
      res << (*foPremise);
    }
    else {
      res << "built-in true!=false";
    }
  }
  else {
    CPair p1= parent._cInfos[c1].namedPair;
    CPair p2= parent._cInfos[c2].namedPair;
    res << "congruence of ("<<p1.first<<","<<p1.second<<") and ("<<p2.first<<","<<p2.second<<")";
  }
  return res.str();
}

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
	addPendingEquality(eq);
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
      addPendingEquality(eq);
    }

    _allAddedLits.push(l);
  }
}

void SimpleCongruenceClosure::addPendingEquality(CEq eq) {
  CALL("SimpleCongruenceClosure::addPendingEquality");

  ASS_G(eq.c1,0);
  ASS_G(eq.c2,0);
  LOG("dp_cc_eqs_pending","pending equality: "<<eq.toString(*this));
  _pendingEqualities.push(eq);
}

/**
 * Invert some edges in the proof tree, so that c becomes the proof root
 */
void SimpleCongruenceClosure::makeProofRepresentant(unsigned c)
{
  CALL("SimpleCongruenceClosure::makeProofRepresentant");

  CEq transfPrem; //initialized as invalid
  unsigned transfParent;
NOT_IMPLEMENTED;
//  _cInfos[c]
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

    LOG("dp_cc_unions","union of "<<curr0.toString(*this)<<" dereferenced as "<<bRep<<"<-"<<aRep);

    ConstInfo& aInfo = _cInfos[aRep];
    ConstInfo& bInfo = _cInfos[bRep];
    ASS_EQ(aInfo.reprConst,0);
    ASS_EQ(bInfo.reprConst,0);
    ASS_EQ(aInfo.proofPredecessor,0);
    ASS_EQ(bInfo.proofPredecessor,0);
    aInfo.proofPredecessor = bRep;
    aInfo.predecessorPremise = curr0;
    aInfo.reprConst = bRep;
    bInfo.classList.push(aRep);
    Stack<unsigned>::Iterator aChildIt(aInfo.classList);
    while(aChildIt.hasNext()) {
      unsigned aChild = aChildIt.next();
      bInfo.classList.push(aChild);
      _cInfos[aChild].reprConst = bRep;
    }
    Stack<unsigned>::Iterator aUseIt(aInfo.useList);
    while(aUseIt.hasNext()) {
      unsigned usePairConst = aUseIt.next();
      CPair usedPair = _cInfos[usePairConst].namedPair;
      ASS(usedPair!=CPair(0,0)); //the constant must be a name of a pair
      CPair derefPair = deref(usedPair);

      unsigned* pDerefPairName;
      if(!_pairNames.getValuePtr(derefPair, pDerefPairName)) {
	addPendingEquality(CEq(*pDerefPairName, usePairConst));
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

/**
 * Return the depth of constant @c c in the tree determined
 * by ConstInfo::proofPredecessor. 0 means @c c is the root.
 */
unsigned SimpleCongruenceClosure::getProofDepth(unsigned c)
{
  CALL("SimpleCongruenceClosure::getProofDepth");

  unsigned res = 0;
  while(_cInfos[c].proofPredecessor!=0) {
    c = _cInfos[c].proofPredecessor;
    res++;
  }
  return res;
}

/**
 * Into @c path put constants so that their predecessorPremise objects
 * imply equality of c1 and c2.
 */
void SimpleCongruenceClosure::collectUnifyingPath(unsigned c1, unsigned c2, Stack<unsigned>& path)
{
  CALL("SimpleCongruenceClosure::collectUnifyingPath");
  ASS_EQ(deref(c1), deref(c2));
  LOG("dp_cc_expl_up","finding unifying path between "<<c1<<" and "<<c2);

  //this function could be probably made more efficient if we use some time-stamping the the ConstInfo object

  unsigned depth1 = getProofDepth(c1);
  unsigned depth2 = getProofDepth(c2);

  if(depth1<depth2) {
    swap(c1,c2);
    swap(depth1,depth2);
  }
  LOG("dp_cc_expl_up","proof depth of c1 "<<c1<<": "<<depth1);
  LOG("dp_cc_expl_up","proof depth of c2 "<<c2<<": "<<depth2);

  while(depth1>depth2) {
    path.push(c1);
    c1 = _cInfos[c1].proofPredecessor;
    depth1--;
    LOG("dp_cc_expl_up","c1 up to "<<c1);
 }

  LOG("dp_cc_expl_up","equal depth of both branches");

#if VDEBUG
  unsigned depth=depth1;
#endif
  while(c1!=c2) {
#if VDEBUG
    ASS_G(depth,0);
    depth--;
#endif
    path.push(c1);
    c1 = _cInfos[c1].proofPredecessor;
    path.push(c2);
    c2 = _cInfos[c2].proofPredecessor;
    LOG("dp_cc_expl_up","c1 up to "<<c1);
    LOG("dp_cc_expl_up","c2 up to "<<c2);
  }
}

void SimpleCongruenceClosure::getUnsatisfiableSubset(LiteralStack& res)
{
  CALL("SimpleCongruenceClosure::getUnsatisfiableSubset");
  ASS(res.isEmpty());
  ASS(!_unsatEq.isInvalid());

  //ineficient but correct: return everything
  res.loadFromIterator(LiteralStack::Iterator(_allAddedLits));
  return;

  LOG("dp_cc_interf_unsat", "UNSAT subset start");

  ASS(_unsatEq.foOrigin);
  if(_unsatEq.foPremise) {
    res.push(_unsatEq.foPremise);
  }

  static Stack<CPair> toExplain;
  toExplain.push(CPair(_unsatEq.c1, _unsatEq.c2));

  IntUnionFind explained(getMaxConst()+1);
  static Stack<unsigned> pathStack;

  while(toExplain.isNonEmpty()) {
    CPair curr = toExplain.pop();
    if(explained.root(curr.first)==explained.root(curr.second)) {
      //we've already explained this equality
      LOG("dp_cc_expl_curr","("<<curr.first<<","<<curr.second<<") already explained");
      continue;
    }
    LOG("dp_cc_expl_curr","("<<curr.first<<","<<curr.second<<") to be explained now");
    pathStack.reset();
    collectUnifyingPath(curr.first, curr.second, pathStack);
    while(pathStack.isNonEmpty()) {
      unsigned proofStepConst = pathStack.pop();
      CEq& prem = _cInfos[proofStepConst].predecessorPremise;
      LOG("dp_cc_expl_prem", "premise: "<<prem.toString(*this));
      if(prem.foOrigin) {
	if(prem.foPremise) {
	  LOG("dp_cc_interf_unsat", *prem.foPremise);
	  res.push(prem.foPremise);
	}
      }
      else {
	//the equality was implied by congruence between the following two pairs:
	CPair cp1 = _cInfos[prem.c1].namedPair;
	CPair cp2 = _cInfos[prem.c2].namedPair;
	ASS_NEQ(cp1.first,0);
	ASS_NEQ(cp1.second,0);
	ASS_NEQ(cp2.first,0);
	ASS_NEQ(cp2.second,0);
	LOG("dp_cc_expl_plan","need to explain ("<<cp1.first<<","<<cp1.second<<")");
	LOG("dp_cc_expl_plan","need to explain ("<<cp2.first<<","<<cp2.second<<")");
	toExplain.push(CPair(cp1.first, cp2.first));
	toExplain.push(CPair(cp1.second, cp2.second));
      }
      explained.doUnion(prem.c1, prem.c2);
    }
  }

  LOG("dp_cc_interf_unsat", "UNSAT subset end");
}


}
