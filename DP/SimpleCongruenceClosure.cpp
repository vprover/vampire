/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
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
#include "Lib/DynamicHeap.hpp"

#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"

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
  // Martin: keep only those namedPairs in useList for which selfIndex
  // is one of the arguments, and keep each such exactly once
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

#if VDEBUG

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


SimpleCongruenceClosure::SimpleCongruenceClosure(Ordering* ord) :
  _ord(ord)
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
unsigned SimpleCongruenceClosure::getSignatureConst(unsigned symbol, SignatureKind kind)
{
  CALL("SimpleCongruenceClosure::getSignatureConst");

  unsigned* pRes;
  if(!_sigConsts.getValuePtr(make_pair(symbol, kind), pRes)) {
    return *pRes;
  }
  unsigned res = getFreshConst();
  _cInfos[res].sigSymbol = symbol;
  _cInfos[res].sigSymKind = kind;
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
    // Martin: if we are here, the above insertion was not needed now,
    // but will become necessary after reset(); see resetEquivalences
    unsigned fRepr = _cInfos[p.first].reprConst;
    _cInfos[fRepr].useList.push(res);
  }
  _cInfos[p.second].useList.push(res);
  if(_cInfos[p.second].reprConst!=0) {
    // Martin: if we are here, the above insertion was not needed now,
    // but will become necessary after reset(); see resetEquivalences
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

    if (t.isTerm()) {
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
      res = _parent.getSignatureConst(t.var(), SignatureKind::VARIABLE);
    }
    else {
      ASS(t.isTerm());
      Term* trm = t.term();
      SignatureKind sk = trm->isSort() ? SignatureKind::TYPECON : SignatureKind::FUNCTION;
      res = _parent.getSignatureConst(trm->functor(), sk);
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
  // Martin: in any case, the logical negation is encoded by the caller;
  // notice that we ignore the polarity below:

  res = getSignatureConst(lit->functor(), SignatureKind::PREDICATE);
  Term::Iterator ait(lit);
  while(ait.hasNext()) {
    TermList a = ait.next();
    unsigned argConst = convertFO(a);
    res = getPairName(CPair(res, argConst));
    //Martin: same way to currify like in FOConversionWorker::post
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
 * - if distinct predicate (a special predicate in the TFF language of TPTP that
 *     guarantees that its arguments are distinct)
 *     add to distinctConstraints or negDistinctConstraints appropriately
 *
 * - otherwise build an integer representative of the term and
 *    if the literal is positive equate it with a positive constant
 *    otherwise, equate it with a negative constant
 *
 */
void SimpleCongruenceClosure::addLiterals(LiteralIterator lits, bool onlyEqualites)
{
  CALL("SimpleCongruenceClosure::addLiterals");
  ASS(!_hadPropagated);

  while(lits.hasNext()) {
    Literal* l = lits.next();
    if(!l->ground()) {
      //for now we ignore non-ground literals
      continue;
      // update: we do handle them, but let's not change the bahavoir of this interface
    }

    if (!onlyEqualites || (l->isEquality() && l->isPositive())) {
      addLiteral(l);
    }
  }
}

void SimpleCongruenceClosure::addLiteral(Literal* lit)
{
  CALL("SimpleCongruenceClosure::addLiteral");

  if (lit->isEquality()) {
    CEq eq = convertFOEquality(lit);

    if (lit->isPositive()) {
      addPendingEquality(eq);
    } else {
      _negEqualities.push(eq);
    }
  } else if(isDistinctPred(lit)) {
    readDistinct(lit);
  } else {
    unsigned predConst = convertFONonEquality(lit);
    CEq eq;
    if(lit->isPositive()) {
      eq = CEq(predConst, _posLitConst, lit);
    }
    else {
      eq = CEq(predConst, _negLitConst, lit);
    }
    addPendingEquality(eq);
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
  
  //Martin: it shouldn't, because we always reorder a path in the smaller proof tree
  
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
      ASS(usedPair!=derefPair); // Martin: (at least) one of the arguments was aRep, now is bRep

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
	continue; // Martin: why not break?
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
    ASS(_unsatEqs.isNonEmpty());
    // Martin: else continue collecting other potential reasons for unsat    
  }

  //The intuition is that we want to fail on as early equalities as possible
  //(to improve back-jumping), so we have a BottomUpIterator here.
  //A possible problem with this is that the non-equality true!=false is the
  //first one, so whenever we have a contradiction with non-equality predicates,
  //it will be discovered first.
  //
  // Giles: not sure why 'early' equalities are better as the order of added literals
  //        is based on order added to SAT solver, which is not necessarily indicative
  //        of ordering in SAT solver splitting tree
  //        Cannot see why true!=false would be first non-equality
  // Martin: agree with first, can explain the second (see the constructor and reset())
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

  //this function could be probably made more efficient if we use some time-stamping of the ConstInfo object
  
  // Martin: paper says, proof can be found in O(k), where k is size of the proof
  // My idea: go from both in parallel and start marking the paths, when one hits
  // a marked node, the other should go back here too and then they both return home, "printing"
  
  // Martin: this is probably not the whole story; some parts of these proofs might have been output already
  // (see the paper for more details) [probably only if this is shown to be a bottleneck]

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
  CALL("SimpleCongruenceClosure::getUnsatCore");
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
	} // Martin: this should be only null for the "built-in" dis-equality (_posLitConst != _negLitConst)
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

struct SimpleCongruenceClosure::ConstOrderingComparator {
  ConstOrderingComparator(DArray<ConstInfo>& cInfos, Ordering& ord) 
    : _cInfos(cInfos), _ord(ord) {}
  
  Comparison compare(unsigned c1, unsigned c2)
  {
    TermList c1NF = _cInfos[c1].normalForm;
    TermList c2NF = _cInfos[c2].normalForm;
    
    // we don't care about the order of partial applications 
    // as long as they are smaller than the proper terms
    
    if (c1NF.isEmpty()) {
      if (c2NF.isEmpty()) {
        return EQUAL;
      } else {
        return LESS;
      }
    } else {
      if (c2NF.isEmpty()) {
        return GREATER;
      } else {
        // We should not be comparing sorts with terms via the ordering
        if(c1NF.term()->isSort() && !c2NF.term()->isSort()){
          return LESS;
        } else if(c2NF.term()->isSort() && !c1NF.term()->isSort()) {
          return GREATER;
        }
        // two proper terms
        switch(_ord.compare(c1NF,c2NF)) {
          case Ordering::Result::GREATER:
            return GREATER;    
          case Ordering::Result::LESS:
            return LESS;
          case Ordering::Result::EQUAL:
            return EQUAL;    
          default:
            ASSERTION_VIOLATION;
        }
      }
    }
  }
  
  DArray<ConstInfo>& _cInfos;
  Ordering& _ord;
};

/**
 * Const @c c is a namedPair and both of its arguments are normalized.
 * 
 * We can compute normal form for @c c, provided it names a term at all.
 */
void SimpleCongruenceClosure::computeConstsNormalForm(unsigned c, NFMap& normalForms) 
{
  CALL("SimpleCongruenceClosure::computeConstsNormalForm");
      
  ConstInfo& cInfo = _cInfos[c];
  if (!cInfo.term.isEmpty() && cInfo.normalForm.isEmpty()) {
    Term* t = cInfo.term.term();
    unsigned idx = t->arity();
    unsigned d = c;
    
    static DArray<TermList> args(8);
    args.ensure(idx);
    while (idx-->0) {
      CPair pair = _cInfos[d].namedPair;
      ASS(pair !=CPair(0,0)); 
      args[idx] = normalForms.get(deref(pair.second));             
      ASS(args[idx].isTerm());
      d = pair.first;
    }
    ASS_EQ(_cInfos[d].sigSymbol,t->functor());
    if(t->isSort()){
      cInfo.normalForm = TermList(AtomicSort::create(static_cast<AtomicSort*>(t),args.array()));
    } else {
      cInfo.normalForm = TermList(Term::create(t,args.array()));
    }
  }
}

/**
 * Return a reduced rewrite system compatible with the current ordering
 * equivalent to the previously given positive equations
 * in the form of a set of equational literals.
 * 
 * Based on the algorithm suggested by Wayne Snyder (1993),
 * A Fast Algorithm for Generating Reduced Ground Rewriting Systems from a Set of Ground Equations.
 */
void SimpleCongruenceClosure::getModel(LiteralStack& model)
{
  CALL("SimpleCongruenceClosure::getModel");
  
  // a heap of candidate constants to process
  static DynamicHeap<unsigned, ConstOrderingComparator, ArrayMap<unsigned> >
    candidates(ConstOrderingComparator(_cInfos,*_ord));
  ASS(candidates.isEmpty());
  
  // a map of already computed normal forms, indexed by class representatives
  static NFMap normalForms;
  normalForms.reset();
  
  unsigned maxConst = getMaxConst();
  candidates.elMap().expand(maxConst+1);
  
  // we process even predicates/literals but they will not show up in the result
  // (because they are not in a class associated with a term)
  
  // moreover, it is encouraged that a separate copy of the SimpleCongruenceClosure
  // is used for the purposes of calling getModel, a copy which never receives predicates or even dis-equalities

  // initialize the info associated with constants
  // and the heap of potential candidates    
  for (unsigned c = 3; // skip 0=unused, 1=_posLitConst and 2=_negLitConst
                c <= maxConst; c++) {
    ConstInfo& cInfo = _cInfos[c];
    
    // cout << "init for " << c;
    
    cInfo.processed = false;    
    cInfo.half_normalized = false;
    cInfo.normalForm.makeEmpty();                
    
    if (cInfo.sigSymbol != NO_SIG_SYMBOL) { // either a symbol ...
      // cout << " is sigsym ";
      
      // this copies the term for constants and an empty termlist for function symbols of arity > 0
      cInfo.normalForm = cInfo.term;
      
      //cout << " and term " << cInfo.term.toString() << endl;      
      //if (cInfo.lit) {
      //  cout << " and a lit " << cInfo.lit->toString() << endl;
      //}
      
      // it is important that the normal form has already been assigned, 
      // since the insertion into the heap starts calling compare
      candidates.insert(c);
    } else { // ... or a named pair      
    	ASS_NEQ(cInfo.namedPair.first,0);
      ASS_NEQ(cInfo.namedPair.second,0);
      
      //cout << " names a pair (" << cInfo.namedPair.first << ", " 
      //                          << cInfo.namedPair.second << ")";
      //cout << " and term " << cInfo.term.toString();      
      //if (cInfo.lit) {
      //  cout << " and a lit " << cInfo.lit->toString();
      //}
      
      unsigned lRep = deref(cInfo.namedPair.first);
      unsigned rRep = deref(cInfo.namedPair.second);
      ASS_NEQ(lRep,c); // the left child is necessarily in a different class
      _cInfos[lRep].upEdges.push(c);
      
      //cout << " adds a left edge to " << lRep;
      
      if (rRep != deref(c)) { // for the right child, don't store upEdges within a class
        _cInfos[rRep].upEdges.push(c);
        
        //cout << " adds a right edge to " << rRep;
      }
      //cout << endl;      
    }
  }
  
  // cout << "processing" << endl;
  
  while (!candidates.isEmpty()) {
    unsigned c = candidates.pop();
    unsigned r = deref(c);
    ConstInfo& rInfo = _cInfos[r];
    
    //cout << "Picking candidate " << c << " with repr " << r << endl;
    
    if (!rInfo.processed) {
      //cout << "Class not processed yet." << endl;
      ConstInfo& cInfo = _cInfos[c];
                  
      rInfo.processed = true;
      if (!cInfo.normalForm.isEmpty()) { // Are we considering a class with true terms (not partial applications)?
        // c was the smallest candidate from this class,
        // we will now keep c's normal form under the index r for everybody "above" to access
        ALWAYS(normalForms.insert(r,cInfo.normalForm));
      }

      Stack<unsigned>::Iterator rUseIt(rInfo.upEdges);
      while(rUseIt.hasNext()) {                
        unsigned s = rUseIt.next(); // a super-term refers to a term in our class

        // Giles suggested an optimization: don't consider terms from already normalized classes as candidates
        if (_cInfos[deref(s)].processed) {
          continue;
        }

        ConstInfo& sInfo = _cInfos[s];
        ASS(sInfo.namedPair!=CPair(0,0)); //must be a name of a pair
        
        // cout << "superterm " << s;
        
        if (sInfo.half_normalized) {                     
          // now becomes fully
          computeConstsNormalForm(s,normalForms);
          
          //cout << " gets its normal form " << sInfo.normalForm.toString();
          
          // and can be inserted among candidates
          candidates.insert(s);
        } else {
          //cout << " becoming half_normalized";
          
          sInfo.half_normalized = true;
        }
        
        //cout << endl;
      }
      // upEdges must be kept clean between the calls to this function
      rInfo.upEdges.reset();
    }
  }
  
  // start preparing the result
  // avoid generating trivial equalities and duplicates (by hashing the pairs)
  NFMap::Iterator nfIt(normalForms);
  while(nfIt.hasNext()) {
    unsigned r;
    TermList nf;
    nfIt.next(r,nf);
    
    //cout << "Outputting for class " << r << " with nf " << nf.toString() << endl;
    
    static DHSet<TermList> seen;
    seen.reset();
    seen.insert(nf); // this way we avoid generating the identity equality
    
    // for the representative
    computeConstsNormalForm(r,normalForms); // maybe calling for a second time, but that's cheap    
    if (!seen.contains(_cInfos[r].normalForm)) {
      //cout << _cInfos[r].normalForm << " -> " << nf << endl;
      model.push(Literal::createEquality(true,_cInfos[r].normalForm,nf,SortHelper::getResultSort(nf.term())));
      seen.insert(_cInfos[r].normalForm);
    }
    
    // and for all other members of the class
    Stack<unsigned>::Iterator classIt(_cInfos[r].classList);
    while (classIt.hasNext()) {
      unsigned c = classIt.next();
      
      computeConstsNormalForm(c,normalForms); // maybe calling for a second time, but that's cheap
      if (!seen.contains(_cInfos[c].normalForm)) {
        //cout << _cInfos[c].normalForm << " -> " << nf << endl;
        model.push(Literal::createEquality(true,_cInfos[c].normalForm,nf,SortHelper::getResultSort(nf.term())));
        seen.insert(_cInfos[c].normalForm);
      }
    }
  }
  
  DEBUG_CODE( assertModelInfoClean(); );  
}

#if VDEBUG
void SimpleCongruenceClosure::assertModelInfoClean() const
{
  CALL("SimpleCongruenceClosure::assertModelInfoClean");
  unsigned maxConst = getMaxConst();
  for (unsigned c = 0; c <= maxConst; c++) {
    const ConstInfo& cInfo = _cInfos[c];
    ASS(cInfo.upEdges.isEmpty());
  }
}
#endif 

}
