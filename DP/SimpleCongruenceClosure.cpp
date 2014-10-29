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

#include "Shell/DistinctProcessor.hpp"

namespace DP
{

const unsigned SimpleCongruenceClosure::NO_SIG_SYMBOL = 0xFFFFFFFF;

vstring SimpleCongruenceClosure::CEq::toString() const
{
  CALL("SimpleCongruenceClosure::CEq::toString");

  vostringstream res;
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

vstring SimpleCongruenceClosure::CEq::toString(SimpleCongruenceClosure& parent) const
{
  CALL("SimpleCongruenceClosure::CEq::toString");

  vostringstream res;
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
  seen.ensure(parent.getMaxConst()+1);
  seen.reset();

  Stack<unsigned>::DelIterator ulit(useList);
  while(ulit.hasNext()) {
    unsigned p = ulit.next();
    ConstInfo& pInfo = parent._cInfos[p];
    if(pInfo.namedPair.first!=selfIndex && pInfo.namedPair.second!=selfIndex) {
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

#ifdef VDEBUG

void SimpleCongruenceClosure::ConstInfo::assertValid(SimpleCongruenceClosure& parent, unsigned selfIndex) const
{
  CALL("SimpleCongruenceClosure::ConstInfo::assertValid");

  if(reprConst==0) {
    Stack<unsigned>::ConstIterator ulit(useList);
    while(ulit.hasNext()) {
      unsigned p = ulit.next();
      ConstInfo& pInfo = parent._cInfos[p];
      CPair pPair = pInfo.namedPair;
      ASS_NEQ(pPair.first,0);
      ASS_NEQ(pPair.second,0);
      CPair derefPair = parent.deref(pPair);
      ASS(derefPair.first==selfIndex || derefPair.second==selfIndex);
    }
  }
}

#endif


SimpleCongruenceClosure::SimpleCongruenceClosure()
{
  CALL("SimpleCongruenceClosure::SimpleCongruenceClosure");

  _cInfos.ensure(1); //this ensures constants will start numbered from 1, not 0

  _posLitConst = getFreshConst();
  _negLitConst = getFreshConst();
  _negEqualities.push(CEq(_posLitConst, _negLitConst, 0));

  _hadPropagated = false;
}

void SimpleCongruenceClosure::reset()
{
  CALL("SimpleCongruenceClosure::reset");

#if 0
  _cInfos.expand(1);
  _sigConsts.reset();
  _pairNames.reset();
  _termNames.reset();
  _litNames.reset();

  _negEqualities.reset();
  _posLitConst = getFreshConst();
  _negLitConst = getFreshConst();
  _negEqualities.push(CEq(_posLitConst, _negLitConst, 0));

#else
  //do reset that keeps the data for converting terms to constants

  unsigned maxConst = getMaxConst();
  for(unsigned i=1; i<=maxConst; i++) {
    _cInfos[i].resetEquivalences(*this, i);
  }

  PairMap::DelIterator pmit(_pairNames);
  while(pmit.hasNext()) {
    CPair namePair;
    unsigned nameConst;
    pmit.next(namePair, nameConst);

    if(_cInfos[nameConst].namedPair!=namePair) {
      pmit.del();
    }
  }

  //this leaves us just with the true!=false non-equality
  _negEqualities.truncate(1);
  ASS_EQ(_negEqualities.top().c1,_posLitConst);
  ASS_EQ(_negEqualities.top().c2,_negLitConst);
#endif

  //no unsat non-equality
  _unsatEqs.reset();

  _pendingEqualities.reset();
  _distinctConstraints.reset();
  _negDistinctConstraints.reset();

  _hadPropagated = false;
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
    CALL("SimpleCongruenceClosure::FOConversionWorker::post");

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
    return res;
  }

  SimpleCongruenceClosure& _parent;
};

/**
 * Convert a first-order term into a canonical constant
 * by traversing the term structure converting each subterm, results are
 * cached in _termNames for consistency
 *
 * (see FOConversionWorker)
 */
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

/**
 * Convert a non-equality term into a canonical constant
 *
 */
unsigned SimpleCongruenceClosure::convertFONonEquality(Literal* lit)
{
  CALL("SimpleCongruenceClosure::convertFONonEquality");
  ASS(!lit->isEquality());

  unsigned res;
  if(_litNames.find(lit, res)) {
    return res;
  }
  if(_litNames.find(Literal::complementaryLiteral(lit), res)) {
    _litNames.insert(lit, res);
    return res;
  }

  res = getSignatureConst(lit->functor(), false);
  Term::Iterator ait(lit);
  while(ait.hasNext()) {
    TermList a = ait.next();
    unsigned argConst = convertFO(a);
    res = getPairName(CPair(res, argConst));
  }
  _cInfos[res].lit = lit;

  _litNames.insert(lit, res);
  return res;
}

/**
 * Uses Shell::DistinctProcessor to check for $distinct predicate from TFF language in TPTP
 */
bool SimpleCongruenceClosure::isDistinctPred(Literal* l)
{
  CALL("SimpleCongruenceClosure::isDistinctPred");

  return Shell::DistinctProcessor::isDistinctPred(l);
}

/**
 * Records distinct arguments (will be used to check satisfiability)
 */
void SimpleCongruenceClosure::readDistinct(Literal* lit)
{
  CALL("SimpleCongruenceClosure::readDistinct");

  bool pos = lit->isPositive();
  DistinctStack& tgtDStack = pos ? _distinctConstraints : _negDistinctConstraints;
  tgtDStack.push(DistinctEntry(lit));
  Stack<unsigned>& tgtStack = tgtDStack.top()._consts;
  Literal::Iterator ait(lit);
  while(ait.hasNext()) {
    TermList arg = ait.next();
    unsigned cNum = convertFO(arg);
    tgtStack.push(cNum);
  }
}

/**
 * Convert a equality literal into a CEq
 * by first converting each side into a representative constant (see convertFO)
 */
SimpleCongruenceClosure::CEq SimpleCongruenceClosure::convertFOEquality(Literal* equality)
{
  CALL("SimpleCongruenceClosure::convertFOEquality(Literal*)");
  ASS(equality->isEquality());

  unsigned arg1 = convertFO(*equality->nthArgument(0));
  unsigned arg2 = convertFO(*equality->nthArgument(1));
  return CEq(arg1, arg2, equality);
}

/**
 * Add literals based on their structure
 * - if non-ground ignore
 *
 * - if equality convert each side to a representative integer and place in a CEq
 *     if positive equality add eq as a pending equality
 *     otherwise add eq to _negEqualities
 *
 * - if distinct predicate (a special predicate in teh TFF language of TPTP that
 *     gaurentees that its arguments are distinct)
 *     add to distinctConstraints or negDistinctConstraints appropriately
 *
 * - otherwise build an integer representative of the term and
 *    if the literal is positive equate it with a positive constant
 *    otherwise, equate it with a negative constant
 *
 */
void SimpleCongruenceClosure::addLiterals(LiteralIterator lits)
{
  CALL("SimpleCongruenceClosure::addLiterals");
  ASS(!_hadPropagated);

  while(lits.hasNext()) {
    Literal* l = lits.next();
    if(!l->ground()) {
      //for now we ignore non-ground literals
      continue;
    }
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
  _pendingEqualities.push_back(eq);
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

/**
 * Propagate any pending equalities
 *
 *
 */
void SimpleCongruenceClosure::propagate()
{
  CALL("SimpleCongruenceClosure::propagate");

  _hadPropagated = true;

  while(_pendingEqualities.isNonEmpty()) {
    CEq curr0 = _pendingEqualities.pop_back();
    CPair curr = deref(curr0);
    if(curr.first==curr.second) {
      continue;
    }
    // Ensure the first constant has a smaller class size
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

    // Get the class representatives
    unsigned aRep = curr.first;
    unsigned bRep = curr.second;

    ConstInfo& aInfo = _cInfos[aRep];
    ConstInfo& bInfo = _cInfos[bRep];
    ASS_EQ(aInfo.reprConst,0); // ensure that they are their own representatives
    ASS_EQ(bInfo.reprConst,0);

    DEBUG_CODE( aInfo.assertValid(*this, aRep); );
    DEBUG_CODE( bInfo.assertValid(*this, bRep); );

    // Merge first class into second (which is why we wanted the first to be smaller)
    // To do this we update the representative for all constants in
    // the class of aRep to be bRep
    aInfo.reprConst = bRep;
    bInfo.classList.push(aRep);
    Stack<unsigned>::Iterator aChildIt(aInfo.classList);
    while(aChildIt.hasNext()) {
      unsigned aChild = aChildIt.next();
      bInfo.classList.push(aChild);
      _cInfos[aChild].reprConst = bRep;
    }
    // Now update all places where aRep has been used as a
    // representative of one of the arguments of a pair
    Stack<unsigned>::Iterator aUseIt(aInfo.useList);
    while(aUseIt.hasNext()) {
      unsigned usePairConst = aUseIt.next();
      CPair usedPair = _cInfos[usePairConst].namedPair;
      ASS(usedPair!=CPair(0,0)); //the constant must be a name of a pair
      CPair derefPair = deref(usedPair);
      ASS(usedPair!=derefPair);

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

bool SimpleCongruenceClosure::checkPositiveDistincts(bool retrieveMultipleCores)
{
  CALL("SimpleCongruenceClosure::checkPositiveDistincts");

  //map from a representative to constant in its class present in the current distinct group
  static ArrayMap<unsigned> reprs;
  reprs.ensure(getMaxConst()+1);

  bool foundConflict = false;

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
	_unsatEqs.push(CEq(c, c2, grp._lit));
	if(!retrieveMultipleCores) {
	  return false;
	}
	foundConflict = true;
      }
      else {
	reprs.insert(rep, c);
      }
    }
  }
  return !foundConflict;
}

DecisionProcedure::Status SimpleCongruenceClosure::checkNegativeDistincts(bool retrieveMultipleCores)
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

/**
 * Decide whether the added literals are satisfiable. The @c retrieveMultipleCores parameter
 * indicates whether, on unsat, we should compute all unsat cores or only the first one
 *
 */
DecisionProcedure::Status SimpleCongruenceClosure::getStatus(bool retrieveMultipleCores)
{
  CALL("SimpleCongruenceClosure::getStatus");

  // Propagate any pending equalities
  propagate();

  // Check classes satisfy distincts (inbuilt predicate stating inequality)
  // Straightforward to check positive distincts against congruence classes
  if(!checkPositiveDistincts(retrieveMultipleCores)) {
    if(!retrieveMultipleCores) {
      return DecisionProcedure::UNSATISFIABLE;
    }
  }

  //The intuition is that we want to fail on as early equialities as possible
  //(to improve back-jumping), so we have a BottomUpIterator here.
  //A possible problem with this is that the non-equality true!=false is the
  //first one, so whenever we have a contradiction with non-equality predicates,
  //it will be discovered first.
  //
  // Giles: not sure why 'early' equalities are better as the order of added literals
  //        is based on order added to SAT solver, which is not necessarily indicative
  //        of ordering in SAT solver splitting tree
  //        Cannot see why true!=false would be first non-equality
  Stack<CEq>::BottomFirstIterator neqIt(_negEqualities);
  while(neqIt.hasNext()) {
    CEq neq = neqIt.next();
    // derNEq is neq with each half converted to its class representative
    CPair derNEq = deref(neq);
    if(derNEq.first==derNEq.second) {
      _unsatEqs.push(neq);
      if(!retrieveMultipleCores) {
	return DecisionProcedure::UNSATISFIABLE;
      }
    }
  }

  // check negative distincts, but might return UNKNOWN as if we don't falsify the
  // distinctness it doesn't mean we can't
  DecisionProcedure::Status ndStatus = checkNegativeDistincts(retrieveMultipleCores);

  if(_unsatEqs.isNonEmpty()) {
    return DecisionProcedure::UNSATISFIABLE;
  }
  if(ndStatus==DecisionProcedure::UNKNOWN) {
    return DecisionProcedure::UNKNOWN;
  }
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

  //this function could be probably made more efficient if we use some time-stamping the the ConstInfo object

  unsigned depth1 = getProofDepth(c1);
  unsigned depth2 = getProofDepth(c2);

  if(depth1<depth2) {
    swap(c1,c2);
    swap(depth1,depth2);
  }

  while(depth1>depth2) {
    path.push(c1);
    c1 = _cInfos[c1].proofPredecessor;
    depth1--;
 }

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
  }
}

/**
 * Retrieve unsatcore @c coreIndex
 * This uses the @c coreIndex violated non-equality to extract a set of literals to explain
 * the violation.
 */
void SimpleCongruenceClosure::getUnsatCore(LiteralStack& res, unsigned coreIndex)
{
  CALL("SimpleCongruenceClosure::getUnsatisfiableSubset");
  ASS(res.isEmpty());
  ASS_L(coreIndex,_unsatEqs.size());

  CEq unsatEq = _unsatEqs[coreIndex];

  ASS(unsatEq.foOrigin);
  if(unsatEq.foPremise) {
    res.push(unsatEq.foPremise);
  }

  static Stack<CPair> toExplain;
  toExplain.push(CPair(unsatEq.c1, unsatEq.c2));
  ASS_EQ(deref(toExplain.top().first), deref(toExplain.top().second));

  IntUnionFind explained(getMaxConst()+1);
  static Stack<unsigned> pathStack;

  while(toExplain.isNonEmpty()) {
    CPair curr = toExplain.pop();
    ASS_EQ(deref(curr.first), deref(curr.second));

    if(explained.root(curr.first)==explained.root(curr.second)) {
      //we've already explained this equality
      continue;
    }
    pathStack.reset();
    // put into pathStack constants whose premises imply the equality
    collectUnifyingPath(curr.first, curr.second, pathStack);
    while(pathStack.isNonEmpty()) {
      unsigned proofStepConst = pathStack.pop();
      CEq& prem = _cInfos[proofStepConst].predecessorPremise;
      if(explained.root(prem.c1)==explained.root(prem.c2)) {
        //we've already explained this equality
        continue;
      }
      if(prem.foOrigin) {
	if(prem.foPremise) {
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
	toExplain.push(CPair(cp1.first, cp2.first));
	ASS_EQ(deref(toExplain.top().first), deref(toExplain.top().second));
	toExplain.push(CPair(cp1.second, cp2.second));
	ASS_EQ(deref(toExplain.top().first), deref(toExplain.top().second));
      }
      explained.doUnion(prem.c1, prem.c2);
    }
  }
}


}
