/**
 * @file AIGCompressor.cpp
 * Implements class AIGCompressor.
 */

#include "Lib/DHMap.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/SharedSet.hpp"
#include "Lib/Environment.hpp"

#include "Inferences/DistinctEqualitySimplifier.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/InterpretedLiteralEvaluator.hpp"
#include "Kernel/Problem.hpp"

#include "Shell/Options.hpp"

#include "Flattening.hpp"
#include "PDUtils.hpp"

#include "AIGCompressor.hpp"

namespace Shell
{

///////////////////////
// BDDAIG
//

void BDDAIG::reset()
{
  CALL("BDDAIG::reset");

  _nextVar = 1;
  _a2bCache.reset();
  _b2aCache.reset();
  _varAtoms.reset();
}

void BDDAIG::loadBDDAssignmentFromProblem(const Problem& prb)
{
  CALL("BDDAIG::loadBDDAssignmentFromProblem");

  static DHSet<unsigned> clauseVars;
  unsigned maxVar = 0;
  const Problem::BDDVarMeaningMap& bvm = prb.getBDDVarMeanings();
  Problem::BDDVarMeaningMap::Iterator bvmIt(bvm);
  while(bvmIt.hasNext()) {
    unsigned var;
    Problem::BDDMeaningSpec spec;
    bvmIt.next(var, spec);

    AIGRef aig;
    if(spec.first) {
      ASS(spec.first->ground());
      ASS(spec.first->isPositive());
      ASS(!spec.second);

      aig = _aig.getLit(spec.first);
    }
    else {
      ASS(spec.second);
      clauseVars.reset();
      spec.second->collectVars(clauseVars);
      Clause::Iterator cit(*spec.second);
      AIGRef inner = _aig.getFalse();
      while(cit.hasNext()) {
	Literal* lit = cit.next();
	inner = _aig.getDisj(inner, _aig.getLit(lit));
      }
      if(clauseVars.isEmpty()) {
	aig = inner;
      }
      else {
	AIG::VarSet* varSet = AIG::VarSet::getFromIterator(DHSet<unsigned>::Iterator(clauseVars));
	aig = _aig.getQuant(false, varSet, inner);
      }
    }

    _varAtoms.insert(var, aig);
    _a2bCache.insert(aig.getPositive(), _bdd->getAtomic(var, aig.polarity()));
    if(var>maxVar) {
      maxVar = var;
    }
  }
  _nextVar = maxVar+1;
}

//////////////////////////
// AIG --> BDD direction
//

/**
 * If BDD corresponding to @c a can be determined in a local way, assign
 * it to @c res and return true. Otherwise leave @c res unchanged and
 * return false.
 */
bool BDDAIG::attemptLocalA2B(AIGRef a, BDDNode*& res)
{
  CALL("BDDAIG::attemptLocalA2B");

  bool neg = !a.polarity();
  if(neg) {
    a = a.neg();
  }

  BDDNode* posRes;
  if(_a2bCache.find(a, posRes)) {
    goto succ;
  }

  if(a.isConjunction()) {
    return false;
  }

  if(a.isAtom() || a.isQuantifier()) {
    unsigned var = _nextVar++;
    posRes = _bdd->getAtomic(var, true);
    _varAtoms.insert(var, a);
    //this is important, or we'll introduce multiple BDD vars for the same atom
    _a2bCache.insert(a, posRes);
  }
  else {
    ASS(a.isPropConst());
    ASS(a.isTrue());
    posRes = _bdd->getTrue();
  }

succ:
  res = neg ? _bdd->negation(posRes) : posRes;
  return true;
}

BDDNode* BDDAIG::bddFromAIGConj(AIGRef node, BDDNode* c1, BDDNode* c2)
{
  CALL("BDDAIG::bddFromAIGConj");
  ASS(c1);
  ASS(c2);

  bool neg = !node.polarity();
  if(neg) {
    node = node.neg();
  }
  BDDNode* posRes = _bdd->conjunction(c1, c2);
  _a2bCache.insert(node, posRes);
  return neg ? _bdd->negation(posRes) : posRes;
}

struct BDDAIG::A2BConjBuildingTask {

  A2BConjBuildingTask(AIGRef a, BDDNode* c1, BDDNode* c2, BDDNode** tgt) : a(a), c1(c1), c2(c2), tgt(tgt) {}

  /** AIG that is to be transformed */
  AIGRef a;
  /** child 1 */
  BDDNode* c1;
  /** child 2 */
  BDDNode* c2;
  /** Where to write the result */
  BDDNode** tgt;

  CLASS_NAME(BDDAIG::A2BConjBuildingTask);
  USE_ALLOCATOR(A2BConjBuildingTask);
};

/**
 * If BDD was built, return true, if task was added, return false.
 * The task will contain reference to @c resTgt, so it must not
 * point to a memory that may be reallocated before the added task
 * is executed.
 */
bool BDDAIG::attemptLocalA2BOrAddTask(AIGRef a, BDDNode** resTgt, Stack<A2BConjBuildingTask*>& taskStack)
{
  CALL("BDDAIG::attemptLocalA2BOrAddTask");

  if(attemptLocalA2B(a, *resTgt)) {
    return true;
  }
  ASS(a.isConjunction());
  BDDNode* c1 = 0;
  BDDNode* c2 = 0;
  attemptLocalA2B(a.parent(0), c1);
  attemptLocalA2B(a.parent(1), c2);
  if(c1 && c2) {
    *resTgt = bddFromAIGConj(a, c1, c2);
    return true;
  }
  A2BConjBuildingTask* task = new A2BConjBuildingTask(a, c1, c2, resTgt);
  taskStack.push(task);
  return false;
}

BDDNode* BDDAIG::a2b(AIGRef a)
{
  CALL("BDDAIG::a2b");

  static Stack<A2BConjBuildingTask*> tasks;
  ASS(tasks.isEmpty());

  BDDNode* res = 0;
  if(attemptLocalA2BOrAddTask(a,&res, tasks)) {
    return res;
  }
  ASS(tasks.isNonEmpty());
  while(tasks.isNonEmpty()) {
    A2BConjBuildingTask* curr = tasks.top();
    if(!curr->c1) {
      attemptLocalA2BOrAddTask(curr->a.parent(0), &curr->c1, tasks);
    }
    if(!curr->c2) {
      attemptLocalA2BOrAddTask(curr->a.parent(1), &curr->c2, tasks);
    }
    if(curr->c1 && curr->c2) {
      //we can finalize the task
      *curr->tgt = bddFromAIGConj(curr->a, curr->c1, curr->c2);

      //The calls to attemptLocalA2BOrAddTask could have added new tasks on
      //the top of the stack, but the fact that both parents of the current
      //task are already evaluated means there was no need for adding new tasks,
      //so the current one is thill on the top.
      ASS_EQ(tasks.top(), curr);
      tasks.pop();
      delete curr;
      continue;
    }
    else {
      //some new task must have been added on the top of the stack, because
      //we still need to figure out BDDs of some of the parents of curr->a
      ASS_NEQ(tasks.top(), curr);
    }
  }
  ASS(res);
  return res;
}

//////////////////////////
// BDD --> AIG direction
//


AIGRef BDDAIG::aigFromCompoundBDD(BDDNode* b, AIGRef tAig, AIGRef fAig)
{
  CALL("BDDAIG::aigFromCompoundBDD");
  ASS(!b->isConst());
  ASS(!tAig.isInvalid());
  ASS(!fAig.isInvalid());

  unsigned var = b->getVar();
  AIGRef decAtom = _varAtoms.get(var);
  AIGRef posBranch = _aig.getDisj(decAtom.neg(), tAig);
  AIGRef negBranch = _aig.getDisj(decAtom, fAig);
  AIGRef res = _aig.getConj(posBranch, negBranch);
  _b2aCache.insert(b, res);
  return res;
}

/**
 * If AIG corresponding to @c b can be determined in a local way, assign
 * it to @c res and return true. Otherwise leave @c res unchanged and
 * return false.
 */
bool BDDAIG::attemptLocalB2A(BDDNode* b, AIGRef& res)
{
  CALL("BDDAIG::attemptLocalB2A");

  if(_b2aCache.find(b, res)) {
    return true;
  }
  if(b->isConst()) {
    if(b->isTrue()) {
      res = _aig.getTrue();
    }
    else {
      ASS(b->isFalse());
      res = _aig.getFalse();
    }
    return true;
  }
  return false;
}

struct BDDAIG::B2ATask
{
  B2ATask(BDDNode* b, AIGRef tAig, AIGRef fAig, AIGRef* tgt) : b(b), tAig(tAig), fAig(fAig), tgt(tgt) {}

  /** AIG that is to be transformed */
  BDDNode* b;
  /** AIG of the true branch */
  AIGRef tAig;
  /** AIG of the false branch */
  AIGRef fAig;
  /** Where to write the result */
  AIGRef* tgt;

  CLASS_NAME(BDDAIG::B2ATask);
  USE_ALLOCATOR(B2ATask);
};

bool BDDAIG::attemptLocalB2AOrAddTask(BDDNode* b, AIGRef* resTgt, Stack<B2ATask*>& taskStack)
{
  CALL("BDDAIG::attemptLocalB2AOrAddTask");

  if(attemptLocalB2A(b, *resTgt)) {
    return true;
  }
  ASS(!b->isConst());
  AIGRef tAig = _aig.getInvalid();
  AIGRef fAig = _aig.getInvalid();
  attemptLocalB2A(b->getPos(), tAig);
  attemptLocalB2A(b->getNeg(), fAig);
  if(!tAig.isInvalid() && !fAig.isInvalid()) {
    *resTgt = aigFromCompoundBDD(b, tAig, fAig);
    return true;
  }
  B2ATask* task = new B2ATask(b, tAig, fAig, resTgt);
  taskStack.push(task);
  return false;
}

AIGRef BDDAIG::naiveB2A(BDDNode* b)
{
  CALL("BDDAIG::naiveB2A");

  static Stack<B2ATask*> tasks;
  ASS(tasks.isEmpty());

  AIGRef res = _aig.getInvalid();
  if(attemptLocalB2AOrAddTask(b,&res, tasks)) {
    return res;
  }
  ASS(tasks.isNonEmpty());
  while(tasks.isNonEmpty()) {
    B2ATask* curr = tasks.top();
    if(curr->tAig.isInvalid()) {
      attemptLocalB2AOrAddTask(curr->b->getPos(), &curr->tAig, tasks);
    }
    if(curr->fAig.isInvalid()) {
      attemptLocalB2AOrAddTask(curr->b->getNeg(), &curr->fAig, tasks);
    }
    if(!curr->tAig.isInvalid() && !curr->fAig.isInvalid()) {
      //we can finalize the task
      *curr->tgt = aigFromCompoundBDD(curr->b, curr->tAig, curr->fAig);

      //The calls to attemptLocalB2AOrAddTask could have added new tasks on
      //the top of the stack, but the fact that both parents of the current
      //task are already evaluated means there was no need for adding new tasks,
      //so the current one is thill on the top.
      ASS_EQ(tasks.top(), curr);
      tasks.pop();
      delete curr;
      continue;
    }
    else {
      //some new task must have been added on the top of the stack, because
      //we still need to figure out AIGs of some of the parents of curr->b
      ASS_NEQ(tasks.top(), curr);
    }
  }
  ASS(!res.isInvalid());
  return res;
}

AIGRef BDDAIG::b2a(BDDNode* b)
{
  CALL("BDDAIG::b2a");

//  return naiveB2A(b);

  //at the bottom of the stack there are the outmost trivial variables
  //if pair::second is true, node is implied, otherwise implying
  static Stack<pair<AIGRef,bool> > trivialRecords;
  trivialRecords.reset();

  bool implied;
  static Stack<BDDNode*> trivialAcc;
  trivialAcc.reset();
  while(!b->isAtomic() && _bdd->findTrivial(b, implied, trivialAcc)) {
    ASS(trivialAcc.isNonEmpty());
    while(trivialAcc.isNonEmpty()) {
      BDDNode* tn = trivialAcc.pop();
      bool pos;
      unsigned var;
      _bdd->parseAtomic(tn, var, pos);
      AIGRef posAtom = _varAtoms.get(var);
      AIGRef atom = pos ? posAtom : posAtom.neg();
      trivialRecords.push(make_pair(atom, implied));
      b = _bdd->assignValue(b, var, pos);
    }
  }

  AIGRef res = naiveB2A(b);
  while(trivialRecords.isNonEmpty()) {
    pair<AIGRef,bool> tr = trivialRecords.pop();
    if(tr.second) {
      res = _aig.getConj(tr.first, res);
    }
    else {
      res = _aig.getDisj(tr.first.neg(), res);
    }
  }
  return res;
}

///////////////////////
// AIGCompressor
//

AIGCompressor::AIGCompressor(AIG& aig, unsigned reqFactorNum, unsigned reqFactorDenom, unsigned maxBddVarCnt)
 : _reqFactorNum(reqFactorNum), _reqFactorDenom(reqFactorDenom),
   _lookUpNeedsImprovement(false),
   _aig(aig), _atr(aig), _ba(aig),
   _ilEval(0)
{
  CALL("AIGCompressor::AIGCompressor");

  _maxBDDVarCnt = maxBddVarCnt;
}

AIGCompressor::~AIGCompressor()
{
  CALL("AIGCompressor::~AIGCompressor");
  delete _ilEval;
}

size_t AIGCompressor::getAIGDagSize(AIGRef aig)
{
  CALL("AIGCompressor::getAIGDagSize");

  if(!aig.polarity()) {
    aig = aig.neg();
  }

  size_t* cacheEntry;
  if(!_aigDagSizeCache.getValuePtr(aig, cacheEntry)) {
    return *cacheEntry;
  }

  static AIGInsideOutPosIterator it;
  it.reset(aig);
  size_t res = countIteratorElements<AIGInsideOutPosIterator&>(it);
  *cacheEntry = res;
  return res;
}

AIGRef AIGCompressor::compress(AIGRef aig)
{
  CALL("AIGCompressor::compress");

  return compressByBDD(aig);
}

/**
 * One AIG cannot be better than the other if it hos more colors or more free variables.
 *
 * Otherwise, if the colors or free variables of one aig are a strict subset of the other,
 * it is better.
 *
 * Otherwise, the smaller AIG is better.
 */
bool AIGCompressor::tryCompareAIGGoodness(AIGRef a1, AIGRef a2, Comparison& res)
{
  CALL("AIGCompressor::compareAIGGoodness");

  if(a1==a2) {
    res = EQUAL;
    return true;
  }
  bool canBeGreater = true;
  bool canBeLess = true;
  Color clr1 = a1.getColor();
  Color clr2 = a2.getColor();
  if(clr1!=clr2) {
    if(clr1==COLOR_TRANSPARENT || clr2==COLOR_INVALID) {
      canBeLess = false;
    }
    else if(clr2==COLOR_TRANSPARENT || clr1==COLOR_INVALID) {
      canBeGreater = false;
    }
    else {
      ASS(clr1==COLOR_LEFT || clr1==COLOR_RIGHT);
      ASS(clr2==COLOR_LEFT || clr2==COLOR_RIGHT);
      return false;
    }
  }
  AIG::VarSet* fv1 = a1.getFreeVars();
  AIG::VarSet* fv2 = a2.getFreeVars();
  if(fv1==fv2) {
    if(!canBeGreater) {
      ASS(canBeLess);
      res = LESS;
    }
    else if(!canBeLess) {
      res = GREATER;
    }
    else {
      size_t a1Sz = getAIGDagSize(a1);
      size_t a2Sz = getAIGDagSize(a1);
      res = Int::compare(a2Sz, a1Sz);
      if(res==EQUAL) {
	//we want equal only on equal nodes
	res = Int::compare(a2.nodeIndex(), a1.nodeIndex());
      }
    }
    return true;
  }
  if(fv1->isSubsetOf(fv2)) {
    if(!canBeGreater) { return false; }
    res = GREATER;
    return true;
  }
  else if(fv2->isSubsetOf(fv1)) {
    if(!canBeLess) { return false; }
    res = LESS;
    return true;
  }
  return false;
}

/**
 * The idea is that even if converting BDD back to AIG doesn't
 * give a nicer AIG, we may use it to discover logical equivalence
 * between AIGs. Therefore we keep a _lookUp table which maps
 * BDDs to AIGs that were smaller than the BDD converted back to AIG.
 * During compression of other nodes we then check this map to see
 * if there wasn't some equivalent node previously.
 *
 * The idea of _lookUpImprovement is that after we add an AIG into the
 * _lookUp, we may see some smaller AIG that is equivalent to it. We will
 * rewrite this AIG into the larger original one, but we keep a note
 * that this smaller AIG is an improvement of the original. In the end
 * we will make one pass that will rewrite the nodes for which we have
 * found an improvement.
 *
 * To know that we need to make this final improving pass, we keep the
 * boolean variable _lookUpNeedsImprovement.
 */
bool AIGCompressor::doHistoryLookUp(AIGRef aig, BDDNode* bdd, AIGRef& tgt)
{
  CALL("AIGCompressor::doHistoryLookUp");

  AIGRef* lookupEntry;
  if(_lookUp.getValuePtr(bdd, lookupEntry)) {
    *lookupEntry = aig;
    if (env.options->showPreprocessing()) {
      env.beginOutput();
      env.out() << "[PP] aig_compr_lookup_added: added lookup for "
              <<bdd<<" to be "<<aig << std::endl;
      env.endOutput();
    }
    return false;
  }
  AIGRef lookupBase = *lookupEntry;
  if(aig==lookupBase) {
    return false;
  }
  ASS(!_lookUpImprovement.find(lookupBase.getPositive())); //we have the best target

  Comparison atCmpResult;
  bool atComparable = tryCompareAIGGoodness(aig, lookupBase, atCmpResult);

  if(!atComparable) {
    return false;
  }
  ASS_REP2(atCmpResult!=EQUAL, aig, lookupBase);
  if(atCmpResult==LESS) {
    tgt = lookupBase;
    if (env.options->showPreprocessing()) {
      env.beginOutput();
      env.out() << "[PP] aig_compr_lookup_hit: bdd look-up hit" << std::endl
              <<"  src: "<<aig<<endl
              <<"  tgt: "<<tgt<<endl;
      env.endOutput();
    }        
    return true;
  }
  ASS_EQ(atCmpResult,GREATER);

  AIGRef imprTgt = _atr.lev0Deref(aig, _lookUpImprovement);

  _lookUpNeedsImprovement = true;
  ALWAYS(_lookUpImprovement.insert(lookupBase, imprTgt));
  *lookupEntry = imprTgt;

  if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] aig_compr_lookup_improvement: bdd look-up improvement" << std::endl
        <<"  src: "<<lookupBase<<endl
        <<"  tgt: "<<imprTgt << std::endl;    
    env.endOutput();
  }  

  if(aig!=imprTgt) {
    if (env.options->showPreprocessing()) {
      env.beginOutput();
      env.out() << "[PP] aig_compr_lookup_hit: bdd look-up improvement from improvement map:" << std::endl
              <<"  src: "<<aig<<endl
              <<"  tgt: "<<tgt<<endl;
      env.endOutput();
    }    
    tgt = imprTgt;
    return true;
  }

  return false;

//  if(atCmpResult==LESS) {
//      AIGWithSize* improvementEntry;
//      if(_lookUpImprovement.getValuePtr(bdd, improvementEntry)) {
//        *improvementEntry = curr;
//      }
//      else {
//        Comparison aiCmpResult;
//        ALWAYS(tryCompareAIGGoodness(curr, *improvementEntry, aiCmpResult));
//        if(aiCmpResult==LESS) {
//  	*improvementEntry = curr;
//        }
//      }
//    }
//
//  if(!atComparable) {
//    AIGRef impr = _atr.lev0Deref(*lookupEntry, _lookUpImprovement);
//    if(!_lookUpImprovement.find(bdd, impr)) {
//      return false;
//    }
//    Comparison aiCmpResult;
//    bool aiComparable = tryCompareAIGGoodness(aig, impr, aiCmpResult);
//    if(!aiComparable) {
//      return false;
//    }
//    if(aiCmpResult==LESS) {
//      _lookUpImprovement.set(bdd, curr);
//    }
//  }
//  else if(atCmpResult==LESS) {
//    AIGWithSize* improvementEntry;
//    if(_lookUpImprovement.getValuePtr(bdd, improvementEntry)) {
//      *improvementEntry = curr;
//    }
//    else {
//      Comparison aiCmpResult;
//      ALWAYS(tryCompareAIGGoodness(curr, *improvementEntry, aiCmpResult));
//      if(aiCmpResult==LESS) {
//	*improvementEntry = curr;
//      }
//    }
//  }
//
//  tgt = lookupEntry->first;
//
//  if(!_lookUpNeedsImprovement) {
//    _lookUpNeedsImprovement = _lookUpImprovement.find(bdd);
//  }
//  return true;
}

void AIGCompressor::doLookUpImprovement(AIGTransformer::RefMap& mapToFix)
{
  CALL("AIGCompressor::doLookUpImprovement");

//  static AIGTransformer::RefMap improvementMap;
//  improvementMap.reset();
//
//  LookUpMap::Iterator imit(_lookUpImprovement);
//  while(imit.hasNext()) {
//    BDDNode* src;
//    AIGWithSize tgt;
//    imit.next(src, tgt);
//
//    AIGRef oldRef;
//    AIGWithSize* lookupEntry;
//    NEVER(_lookUp.getValuePtr(src, lookupEntry));
//    oldRef = lookupEntry->first;
//    *lookupEntry = tgt;
//
//    improvementMap.insert(oldRef, tgt.first);
//  }

  static AIGInsideOutPosIterator mapRangeIt;
  mapRangeIt.reset();

  AIGTransformer::RefMap::Iterator mtfIt(mapToFix);
  while(mtfIt.hasNext()) {
    AIGRef rngEl = mtfIt.next();
    mapRangeIt.addToTraversal(rngEl);
  }

  static AIGTransformer::RefMap improvementFullMap;
  improvementFullMap.reset();
  while(mapRangeIt.hasNext()) {
    AIGRef tgt = mapRangeIt.next();

    AIGRef imprTgt = AIGTransformer::lev0Deref(tgt, _lookUpImprovement);
    if(imprTgt==tgt) {
      imprTgt = _atr.lev1Deref(tgt, improvementFullMap);
      if (imprTgt!=tgt && env.options->showPreprocessing()) {
        env.beginOutput();
        env.out() << "[PP] aig_compr_lookup_map_improvement: bdd look-up deref1 improvement in map:" << std::endl
                <<"  src: "<<tgt<<endl
                <<"  tgt: "<<imprTgt<<endl;
        env.endOutput();
      }      
    }
    else {
      if (env.options->showPreprocessing()) {
        env.beginOutput();
        env.out() << "[PP] aig_compr_lookup_map_improvement: bdd look-up deref0 improvement in map:" << std::endl
                <<"  src: "<<tgt<<endl
                <<"  tgt: "<<imprTgt<<endl;
        env.endOutput();
      }     
    }
    if(imprTgt==tgt) {
      //no improvement
      continue;
    }
    improvementFullMap.insert(tgt.getPositive(), tgt.polarity() ? imprTgt : imprTgt.neg());
  }

  AIGTransformer::RefMap::DelIterator mtfRwrIt(mapToFix);
  while(mtfRwrIt.hasNext()) {
    AIGRef val = mtfRwrIt.next();
    AIGRef tgt = AIGTransformer::lev0Deref(val, improvementFullMap);
    if(tgt!=val) {
      if (env.options->showPreprocessing()) {
        env.beginOutput();
        env.out() << "[PP] aig_compr_lookup_map_improvement: bdd look-up improvement in map:" << std::endl
                <<"  src: "<<val<<endl
                <<"  tgt: "<<tgt<<endl;
        env.endOutput();
      }      
      ASS(tgt.getFreeVars()->isSubsetOf(val.getFreeVars()));
      mtfRwrIt.setValue(tgt);
    }
  }

  _lookUpImprovement.reset();
  _lookUpNeedsImprovement = false;
}

/**
 * Do a local compression on BDD that treats quantifier nodes as atomic.
 * If no compression was achieved, leave tgt unchanged.
 */
bool AIGCompressor::localCompressByBDD(AIGRef aig, AIGRef& tgt, bool historyLookUp, bool& usedLookUp)
{
  CALL("AIGCompressor::localCompressByBDD");

  usedLookUp = false;
  if(!aig.isConjunction() ||
      (!aig.parent(0).isConjunction() && !aig.parent(1).isConjunction())) { return false; }

  BDDNode* bRep = _ba.a2b(aig);
  AIGRef aCompr = _ba.b2a(bRep);

  if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] aig_compr_bdd: aig compr:" << std::endl
            <<"  src: "<<aig.toString()<<endl
            <<"  tgt: "<<aCompr.toString()<<endl
            <<"  bdd: "<<BDD::instance()->toTPTPString(bRep, "n")<<endl;
    env.endOutput();
  }
  
  if(aCompr==aig) {
    return false;
  }

  size_t origSz = getAIGDagSize(aig);
  size_t comprSz = getAIGDagSize(aCompr);

  if (comprSz>origSz && env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] aig_compr_growth: aig compr growth: " << std::endl
            <<"  src: "<<aig.toString()<<endl
            <<"  tgt: "<<aCompr.toString()<<endl;
    env.endOutput();
  }  
  
  if(comprSz>=origSz) {
    if(historyLookUp) {
      usedLookUp = true;
      return doHistoryLookUp(aig, bRep, tgt);
    }
    return false;
  }
  tgt = aCompr;
  if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] aig_compr_loc_succ: aig compr local success:" << std::endl
            <<"  src: "<< aig.toString()<<endl
            <<"  tgt: "<< aCompr.toString()<< std::endl;
    env.endOutput();
  }  
  return true;
}

AIGRef AIGCompressor::tryCompressAtom(AIGRef atom)
{
  CALL("AIGCompressor::tryCompressAtom");
  ASS(atom.isAtom());

  if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] aig_compr_atom: trying to compress atom "<<atom << std::endl;
    env.endOutput();
  }

  bool isNeg = !atom.polarity();
  Literal* lit0 = atom.getPositiveAtom();
  Literal* lit = lit0;

  if(lit->isEquality()) {
    unsigned distGroup;
    if(*lit->nthArgument(0)==*lit->nthArgument(1)) {
      if (env.options->showPreprocessing()) {
        env.beginOutput();
        env.out() << "[PP] aig_compr_atom: compressed trivial equality" << std::endl;
        env.endOutput();
      }
      return isNeg ? _aig.getFalse() : _aig.getTrue();
    }
    if(Inferences::DistinctEqualitySimplifier::mustBeDistinct(*lit->nthArgument(0), *lit->nthArgument(1), distGroup)) {
      if (env.options->showPreprocessing()) {
        env.beginOutput();
        env.out() << "[PP] aig_compr_atom: compressed distinct equality" << std::endl;
        env.endOutput();
      }
//      if(distGroup<=Signature::LAST_BUILT_IN_DISTINCT_GROUP) {
	return isNeg ? _aig.getTrue() : _aig.getFalse();
//      }
    }
  }

  if(lit->hasInterpretedConstants()) {
    if(!_ilEval) {
      _ilEval = new InterpretedLiteralEvaluator();
    }
    bool isConst;
    bool constVal;
    Literal* litVal;
    if(_ilEval->evaluate(lit, isConst, litVal, constVal)) {
      if(isConst) {
        if (env.options->showPreprocessing()) {
          env.beginOutput();
          env.out() << "[PP] aig_compr_atom: compressed interpreted tautology" << std::endl;
          env.endOutput();
        }
	return (constVal^isNeg) ? _aig.getTrue() : _aig.getFalse();
      }
      else {
	lit = litVal;
      }
    }
  }
  if(lit==lit0) {
    if (env.options->showPreprocessing()) {
      env.beginOutput();
      env.out() << "[PP] aig_compr_atom: no compression achieved" << std::endl;
      env.endOutput();
    }
    return atom;
  }
  else {
    AIGRef newPos = _aig.getLit(lit);
    if (env.options->showPreprocessing()) {
      env.beginOutput();
      env.out() << "[PP] aig_compr_atom: compressed to atom "<<(isNeg ? newPos.neg() : newPos) << std::endl;
      env.endOutput();
    }
    return isNeg ? newPos.neg() : newPos;
  }
}

AIGCompressor::USharedSet* AIGCompressor::getUnsplittableSet(AIGRef a0, UnsplittableSetMap& cache)
{
  CALL("AIGCompressor::getUnsplittableSet");

  USharedSet* res;
  if(tryGetUnsplittableSetLocally(a0, cache, res, true)) {
    return res;
  }

  ASS(a0.isConjunction());

  static DHSet<AIGRef> seen;
  seen.reset();
  static Stack<AIGRef> toDo;
  toDo.push(a0.parent(0));
  toDo.push(a0.parent(1));
  while(toDo.isNonEmpty()) {
    AIGRef a = toDo.top();
    USharedSet* dummy;
    if(tryGetUnsplittableSetLocally(a, cache, dummy, true)) {
      toDo.pop();
      continue;
    }
    toDo.push(a.parent(0));
    toDo.push(a.parent(1));
  }
  ALWAYS(tryGetUnsplittableSetLocally(a0, cache, res, true));
  return res;
}

AIGCompressor::USharedSet* AIGCompressor::conjGetUnsplittableSet(USharedSet* p1set, USharedSet* p2set)
{
  CALL("AIGCompressor::conjGetUnsplittableSet");

  USharedSet* res;
  if(p1set && p2set) {
    res = p1set->getUnion(p2set);
    if(res->size()>_maxBDDVarCnt) {
      res = 0;
    }
  }
  else {
    res = 0;
  }
  return res;
}

bool AIGCompressor::tryGetUnsplittableSetLocally(AIGRef a, UnsplittableSetMap& cache, USharedSet*& res, bool doOneUnfolding)
{
  CALL("AIGCompressor::tryGetUnsplittableSetLocally");

  if(a.isPropConst()) {
    res = USharedSet::getEmpty();
    return true;
  }
  else if(a.isAtom() || a.isQuantifier()) {
    res = USharedSet::getSingleton(a.nodeIndex());
    return true;
  }

  a = a.getPositive();

  if(cache.find(a, res)) {
    return true;
  }

  if(!doOneUnfolding) {
    return false;
  }


  ASS(a.isConjunction());
  AIGRef p1 = a.parent(0);
  AIGRef pp1 = p1.getPositive();
  AIGRef p2 = a.parent(1);
  AIGRef pp2 = p2.getPositive();

  USharedSet* pp1r;
  if(!tryGetUnsplittableSetLocally(pp1, cache, pp1r, false)) {
    return false;
  }
  USharedSet* pp2r;
  if(!tryGetUnsplittableSetLocally(pp2, cache, pp2r, false)) {
    return false;
  }

  res = conjGetUnsplittableSet(pp1r, pp2r);
  cache.insert(a, res);
  return true;
}

void AIGCompressor::populateBDDCompressingMap(AIGInsideOutPosIterator& aigIt, AIGTransformer::RefMap& map)
{
  CALL("AIGCompressor::populateBDDCompressingMap");
  ASS(_lookUpImprovement.isEmpty());
  ASS(!_lookUpNeedsImprovement);
  
  /** For processed AIGs contains set of refered atoms, or zero
   * if the set of processed atoms was too big. */
  static DHMap<AIGRef,USharedSet*> refAtoms;
  refAtoms.reset();

  while(aigIt.hasNext()) {
    AIGRef a = aigIt.next();
    USharedSet* ref;

    ASS(!map.find(a));
    AIGRef tgt = _atr.lev1Deref(a, map);

    if(tgt.isAtom()) {
      tgt = tryCompressAtom(tgt);
    }

    ref = getUnsplittableSet(tgt, refAtoms);

    //non-zero ref at this point means that the AIG is simple enough to perform BDD sweeping on it
    if(tgt.isConjunction() && ref) {
      bool usedLookUp;
      AIGRef lcTgt;
      localCompressByBDD(tgt, tgt, true, usedLookUp);
//      localCompressByBDD(tgt, tgt, false, usedLookUp);
    }
    if(a!=tgt) {
      map.insert(a, tgt);
      aigIt.addToTraversal(tgt);
    }
  }

  if(_lookUpNeedsImprovement) {
    doLookUpImprovement(map);
  }
}

AIGRef AIGCompressor::attemptCompressByBDD(AIGRef aig0)
{
  CALL("AIGCompressor::attemptCompressByBDD");

  static AIGTransformer::RefMap map;
  map.reset();

  static AIGInsideOutPosIterator aigIt;
  aigIt.reset(aig0);

  populateBDDCompressingMap(aigIt, map);

  AIGRef res = _atr.lev0Deref(aig0, map);

  if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] aig_compr_attempts: aig compression attempt:"<<endl
            <<"  src: "<<aig0<<endl
            <<"  tgt: "<<res << std::endl;
    env.endOutput();
  }
  return res;
}

AIGRef AIGCompressor::compressByBDD(AIGRef aig)
{
  CALL("AIGCompressor::compressByBDD");

  AIGRef aCompr = attemptCompressByBDD(aig);

  if(aCompr==aig) {
    return aig;
  }

  size_t origSz = getAIGDagSize(aig);
  size_t comprSz = getAIGDagSize(aCompr);

  if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] aig_compr_all: aig compr: " << std::endl
      <<"  src("<<origSz<<"): "<<aig.toString()<<endl
      <<"  tgt("<<comprSz<<"): "<<aCompr.toString()<<endl;
    env.endOutput();
  }
  
  if(origSz*_reqFactorDenom>comprSz*_reqFactorNum) {
    if (env.options->showPreprocessing()) {
      env.beginOutput();
      env.out() << "[PP] aig_compr_succ: aig compr succeeded: "<<endl
              <<"  src: "<<aig.toString()<<endl
              <<"  tgt: "<<aCompr.toString()<<endl;              
      env.endOutput();
    }
    return aCompr;
  }
  else {
    return aig;
  }
}


//////////////////////////////
// AIGCompressingTransformer
//

AIGCompressingTransformer::AIGCompressingTransformer(unsigned maxBddVarCnt)
 : _compr(_fsh.aig(),1,1,maxBddVarCnt)
{
  CALL("AIGCompressingTransformer::AIGCompressingTransformer");
}

/**
 * Return simplified formula or 0 if it was tautology
 */
Formula* AIGCompressingTransformer::apply(Formula* f)
{
  CALL("AIGCompressingTransformer::apply/1");

  if(f->connective()==LITERAL) {
    //we cannot compress formulas consisting just of atoms
    return f;
  }

  
  AIGRef fAig = _fsh.apply(f).second;
  AIGRef simpl = _compr.compress(fAig);
  if(simpl==fAig) {
    return f;
  }
  if(simpl.isTrue()) {
    if (env.options->showPreprocessing()) {
      env.beginOutput();
      env.out() << "[PP] aig_compr_forms: aig compr forms"<<endl
              <<"  src: "<<(*f)<<endl
              <<"  tgt: $true" <<endl;
      env.endOutput();
    }
    return 0;
  }
  Formula* res = _fsh.aigToFormula(simpl);
  if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] aig_compr_forms: aig compr forms"<<endl
            <<"  src: "<<(*f)<<endl
            <<"  tgt: "<<(*res)<<endl;
    env.endOutput();
  }
  return res;
}

/**
 * Apply the simplification to a predicate definition,
 * making sure that the definition shape is preserved.
 */
bool AIGCompressingTransformer::applyToDefinition(FormulaUnit* unit, Unit*& res)
{
  CALL("AIGCompressingTransformer::applyToDefinition");

  if(PDUtils::isPredicateEquivalence(unit)) {
    return false;
  }

  Literal* lhs;
  Formula* rhs;
  PDUtils::splitDefinition(unit, lhs, rhs);
  Formula* rhsSimpl = apply(rhs);
  if(rhs==rhsSimpl) {
    return false;
  }
  Formula* lhsf = new AtomicFormula(lhs);
  Formula* f;
  if(!rhsSimpl || rhsSimpl->connective()==TRUE) {
    f = lhsf;
  }
  else if(rhsSimpl->connective()==FALSE) {
    f = new AtomicFormula(Literal::complementaryLiteral(lhs));
  }
  else {
    f = new BinaryFormula(IFF, lhsf, rhsSimpl);
  }
  //it's ehough to get free variables of the lhs, because all free
  //variables of rhs must be in lhs as well
  Formula::VarList* vars = lhsf->freeVariables();
  if(vars) {
    f = new QuantifiedFormula(FORALL, vars, f);
  }

  FormulaUnit* res0 = new FormulaUnit(f, new Inference1(Inference::LOCAL_SIMPLIFICATION, unit), unit->inputType());

  res = Flattening::flatten(res0);
    
  if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] aig_compr_units: simplification:" << endl          
       << "   <- " << unit->toString() << endl
       << "   -> " << res->toString() << endl;
    env.endOutput();
  }

  return true;
}

bool AIGCompressingTransformer::apply(FormulaUnit* unit, Unit*& res)
{
  CALL("AIGCompressingTransformer::apply/2");

  if(PDUtils::hasDefinitionShape(unit)) {
    return applyToDefinition(unit, res);
  }

  Formula* f = unit->formula();
  Formula* fSimpl = apply(f);
  if(f==fSimpl) {
    return false;
  }
  if(!fSimpl) {
    res = 0;
    return true;
  }
  FormulaUnit* res0 = new FormulaUnit(fSimpl, new Inference1(Inference::LOCAL_SIMPLIFICATION, unit), unit->inputType());
  res = Flattening::flatten(res0);
    
  if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] aig_compr_units: simplification:" << endl
              << "   <- " << unit->toString() << endl
              << "   -> " << res->toString() << endl;
    env.endOutput();
  }
  
  return true;
}

void AIGCompressingTransformer::updateModifiedProblem(Problem& prb)
{
  CALL("AIGCompressingTransformer::updateModifiedProblem");

  prb.invalidateProperty();
}

}
