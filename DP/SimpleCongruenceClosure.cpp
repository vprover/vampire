/**
 * @file SimpleCongruenceClosure.cpp
 * Implements class SimpleCongruenceClosure.
 */

#include <sstream>

#include "SimpleCongruenceClosure.hpp"

#include "Lib/ArrayMap.hpp"

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

void SimpleCongruenceClosure::ConstInfo::init() {
  CALL("SimpleCongruenceClosure::ConstInfo::init");

  sigSymbol = NO_SIG_SYMBOL;
  term.makeEmpty();
  lit = 0;
  namedPair = CPair(0,0);
  reprConst = 0;
  proofPredecessor = 0;
  predecessorPremise = CEq(0,0);
  classList.reset();
  useList.reset();
}

void SimpleCongruenceClosure::ConstInfo::resetEquivalences(SimpleCongruenceClosure& parent, unsigned selfIndex) {
  CALL("SimpleCongruenceClosure::ConstInfo::resetEquivalences");

  reprConst = 0;
  proofPredecessor = 0;
  predecessorPremise = CEq(0,0);
  classList.reset();

  static ArraySet seen;
  seen.reset();

  Stack<unsigned>::DelIterator ulit(useList);
  while(ulit.hasNext()) {
    unsigned p = ulit.next();
    ConstInfo& pInfo = parent._cInfos[p];
    if(pInfo.namedPair.first!=p && pInfo.namedPair.second!=p) {
      ulit.del();
      continue;
    }
    if(seen.find(p)) {
      ulit.del();
      continue;
    }
    seen.insert(p);
  }
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

void SimpleCongruenceClosure::reset()
{
  CALL("SimpleCongruenceClosure::reset");

#if 1
  ASS_EQ(_posLitConst,1);
  ASS_EQ(_negLitConst,2);
  //this leaves us just with the true and false constants
  _cInfos.expand(3);

  _sigConsts.reset();
  _pairNames.reset();
  _termNames.reset();

#else
  //do reset that keeps the data for converting terms to constants

  unsigned maxConst = getMaxConst();
  for(unsigned i=1; i<=maxConst; i++) {
    _cInfos[i].resetEquivalences(*this, i);
  }
#endif

  //this leaves us just with the true!=false non-equality
  _negEqualities.truncate(1);
  ASS_EQ(_negEqualities.top().c1,_posLitConst);
  ASS_EQ(_negEqualities.top().c2,_negLitConst);

  //no unsat non-equality
  _unsatEq = CEq(0,0);

  _pendingEqualities.reset();
  _distinctConstraints.reset();
  _negDistinctConstraints.reset();
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
  if(_cInfos[p.first].reprConst!=0) {
    unsigned fRepr = _cInfos[p.first].reprConst;
    _cInfos[fRepr].useList.push(res);
  }
  _cInfos[p.second].useList.push(res);
  if(_cInfos[p.second].reprConst!=0) {
    unsigned sRepr = _cInfos[p.second].reprConst;
    _cInfos[sRepr].useList.push(res);
  }

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

  unsigned cachedRes;
  if(_termNames.find(trm, cachedRes)) {
    return cachedRes;
  }

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

bool SimpleCongruenceClosure::isDistinctPred(Literal* l)
{
  CALL("SimpleCongruenceClosure::isDistinctPred");

  //this is a hacky way to check for disctnct predicates,
  //needs to be fixed once we have a proper sopport for
  //these in the signature
  return l->predicateName().substr(0,9)=="$distinct";
}

void SimpleCongruenceClosure::readDistinct(Literal* lit)
{
  CALL("SimpleCongruenceClosure::readDistinct");

  LOG("dp_cc_distinct","adding distinct constraint "<<(*lit));

  bool pos = lit->isPositive();
  DistinctStack& tgtDStack = pos ? _distinctConstraints : _negDistinctConstraints;
  tgtDStack.push(DistinctEntry(lit));
  Stack<unsigned>& tgtStack = tgtDStack.top()._consts;
  Literal::Iterator ait(lit);
  while(ait.hasNext()) {
    TermList arg = ait.next();
    unsigned cNum = convertFO(arg);
    tgtStack.push(cNum);
    LOG("dp_cc_distinct","  dist const "<<arg<<" represented as number "<<cNum);
  }
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
    else if(isDistinctPred(l)) {
      readDistinct(l);
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

  if(_cInfos[c].proofPredecessor==0) {
    return;
  }

  //this kind of traversal may possibly cause quadratic complexity!

  CEq transfPrem; //initialized as invalid
  unsigned prevC = 0;

  do{
    unsigned newC = _cInfos[c].proofPredecessor;
    _cInfos[c].proofPredecessor = prevC;
    swap(_cInfos[c].predecessorPremise, transfPrem);
    prevC = c;
    c = newC;
  } while(c!=0);
  ASS(transfPrem.isInvalid()); //the proof tree root has invalid equality as a premise
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
      std::swap(curr0.c1, curr0.c2);
      std::swap(curr.first, curr.second);
    }

    {
      //proof updating
      unsigned aProofRep = curr0.c1;
      unsigned bProofRep = curr0.c2;
      makeProofRepresentant(aProofRep);
      ConstInfo& aProofInfo = _cInfos[aProofRep];
      ASS_EQ(aProofInfo.proofPredecessor,0);
      aProofInfo.proofPredecessor = bProofRep;
      aProofInfo.predecessorPremise = curr0;
    }

    unsigned aRep = curr.first;
    unsigned bRep = curr.second;

    LOG("dp_cc_unions","union of "<<curr0.toString(*this)<<" dereferenced as "<<bRep<<"<-"<<aRep);

    ConstInfo& aInfo = _cInfos[aRep];
    ConstInfo& bInfo = _cInfos[bRep];
    ASS_EQ(aInfo.reprConst,0);
    ASS_EQ(bInfo.reprConst,0);

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

bool SimpleCongruenceClosure::checkPositiveDistincts()
{
  CALL("SimpleCongruenceClosure::checkPositiveDistincts");

  //map from a representative to constant in its class present in the current distinct group
  static ArrayMap<unsigned> reprs;
  reprs.ensure(getMaxConst()+1);

  DistinctStack::BottomFirstIterator distIt(_distinctConstraints);
  while(distIt.hasNext()) {
    const DistinctEntry& grp = distIt.next();

    reprs.reset();
    Stack<unsigned>::ConstIterator git(grp._consts);
    while(git.hasNext()) {
      unsigned c = git.next();
      unsigned rep = deref(c);
      unsigned c2;
      if(reprs.find(rep, c2)) {
	//we're unsat, two equal constants in a distinct group
	_unsatEq = CEq(c, c2, grp._lit);
	return false;
      }
      reprs.insert(rep, c);
    }
  }
  return true;
}

DecisionProcedure::Status SimpleCongruenceClosure::checkNegativeDistincts()
{
  //map from a representative to constant in its class present in the current distinct group
  static ArrayMap<unsigned> reprs;
  reprs.ensure(getMaxConst()+1);

  DistinctStack::BottomFirstIterator distIt(_negDistinctConstraints);
  while(distIt.hasNext()) {
    const DistinctEntry& grp = distIt.next();

    reprs.reset();
    bool isFalse = false;
    Stack<unsigned>::ConstIterator git(grp._consts);
    while(git.hasNext()) {
      unsigned c = git.next();
      unsigned rep = deref(c);
      if(reprs.find(rep)) {
	//distinct constraint is false, we're happy
	isFalse = true;
	continue;
      }
      reprs.insert(rep, c);
    }
    if(!isFalse) {
      //The distinct predicate wasn't falsified by the current rewriting system.
      //It might still be possible to extend the system to make the distinct
      //falsified (hence the result UNKNOWN), but we do not implement this.
      return DecisionProcedure::UNKNOWN;
    }
  }
  return DecisionProcedure::SATISFIABLE;
}

DecisionProcedure::Status SimpleCongruenceClosure::getStatus()
{
  CALL("SimpleCongruenceClosure::getStatus");

  propagate();

  if(!checkPositiveDistincts()) {
    LOG("dp_cc_contr", "contradiction: ("<<_unsatEq.c1<<","<<_unsatEq.c2<<") from "<<(*_unsatEq.foPremise)<<" are equal");
    LOG("dp_cc_interf_res","cc gave UNSAT");
    return DecisionProcedure::UNSATISFIABLE;
  }

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

  DecisionProcedure::Status ndStatus = checkNegativeDistincts();
  switch(ndStatus) {
  case DecisionProcedure::UNSATISFIABLE:
    LOG("dp_cc_interf_res","cc gave UNSAT");
    return DecisionProcedure::UNSATISFIABLE;
  case DecisionProcedure::UNKNOWN:
    LOG("dp_cc_interf_res","cc gave UNKNOWN because of the presence of negative $distinct literals");
    return DecisionProcedure::UNSATISFIABLE;
  case DecisionProcedure::SATISFIABLE:
    break;
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

  LOG("dp_cc_interf_unsat", "UNSAT subset start");

  ASS(_unsatEq.foOrigin);
  if(_unsatEq.foPremise) {
    LOG("dp_cc_interf_unsat", *_unsatEq.foPremise);
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
      if(explained.root(prem.c1)==explained.root(prem.c2)) {
        //we've already explained this equality
        LOG("dp_cc_expl_curr","("<<prem.c1<<","<<prem.c2<<") already explained");
        continue;
      }
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
	LOG("dp_cc_expl_planned","need to explain ("<<cp1.first<<","<<cp1.second<<")");
	LOG("dp_cc_expl_planned","need to explain ("<<cp2.first<<","<<cp2.second<<")");
	toExplain.push(CPair(cp1.first, cp2.first));
	toExplain.push(CPair(cp1.second, cp2.second));
      }
      explained.doUnion(prem.c1, prem.c2);
    }
  }

  LOG("dp_cc_interf_unsat", "UNSAT subset end");
}


}
