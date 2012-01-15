/**
 * @file AIGCompressor.cpp
 * Implements class AIGCompressor.
 */

#include "Lib/DHMap.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/SharedSet.hpp"

#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Problem.hpp"

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

  CLASS_NAME("BDDAIG::ConjBuildingTask");
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

  CLASS_NAME("BDDAIG::B2ATask");
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
  while(_bdd->findTrivial(b, implied, trivialAcc)) {
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
    if(b->isAtomic()) {
      break;
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

AIGCompressor::AIGCompressor(AIG& aig, unsigned reqFactorNum, unsigned reqFactorDenom)
 : _reqFactorNum(reqFactorNum), _reqFactorDenom(reqFactorDenom), _aig(aig), _atr(aig), _ba(aig)
{
  CALL("AIGCompressor::AIGCompressor");

  _maxBDDVarCnt = 16;
}

size_t AIGCompressor::getAIGDagSize(AIGRef aig)
{
  static AIGInsideOutPosIterator it;
  it.reset(aig);
  return countIteratorElements<AIGInsideOutPosIterator&>(it);
}

AIGRef AIGCompressor::compress(AIGRef aig)
{
  CALL("AIGCompressor::compress");

  return compressByBDD(aig);
}

/**
 * Do a local compression on BDD that treats quantifier nodes as atomic.
 * If no compression was achieved, leave tgt unchanged.
 */
bool AIGCompressor::localCompressByBDD(AIGRef aig, AIGRef& tgt)
{
  CALL("AIGCompressor::localCompressByBDD");

  if(!aig.isConjunction() ||
      (!aig.parent(0).isConjunction() && !aig.parent(1).isConjunction())) { return false; }

  _ba.reset();
  BDDNode* bRep = _ba.a2b(aig);
  AIGRef aCompr = _ba.b2a(bRep);

  LOG("pp_aig_compr_bdd","aig compr: "<<endl
      <<"  src: "<<aig.toString()<<endl
      <<"  tgt: "<<aCompr.toString()<<endl
      <<"  bdd: "<<BDD::instance()->toTPTPString(bRep, "n"));

  if(aCompr==aig) {
    return false;
  }

  size_t origSz = getAIGDagSize(aig);
  size_t comprSz = getAIGDagSize(aCompr);

  COND_LOG("pp_aig_compr_growth",comprSz>origSz,"aig compr growth: "<<endl<<"  src: "<<aig.toString()<<endl<<"  tgt: "<<aCompr.toString());

  if(comprSz>=origSz) {
    return false;
  }
  tgt = aCompr;
  LOG("pp_aig_compr_loc_succ","aig compr local success: "<<endl<<"  src: "<<aig.toString()<<endl<<"  tgt: "<<aCompr.toString());
  return true;
}

AIGRef AIGCompressor::attemptCompressByBDD(AIGRef aig0)
{
  CALL("AIGCompressor::attemptCompressByBDD");

  static AIGTransformer::RefMap map;
  map.reset();

  typedef SharedSet<unsigned> USharedSet;
  /** For processed AIGs contains set of refered atoms, or zero
   * if the set of processed atoms was too big. */
  static DHMap<AIGRef,USharedSet*> refAtoms;
  refAtoms.reset();

  static AIGInsideOutPosIterator aigIt;
  aigIt.reset(aig0);

  while(aigIt.hasNext()) {
    AIGRef a = aigIt.next();
    USharedSet* ref;
    if(a.isPropConst()) {
      ref = USharedSet::getEmpty();
    }
    else if(a.isAtom()) {
      ref = USharedSet::getSingleton(a.nodeIndex());
    } else if(a.isQuantifier()) {
      ref = USharedSet::getSingleton(a.nodeIndex());

//      AIGRef pp = a.parent(0).getPositive();
//      if(!map.find(pp) && refAtoms.get(pp)) {
//	AIGRef ppTgt = pp;
//	localCompressByBDD(pp, ppTgt);
//	map.insert(pp, ppTgt);
//      }
    }
    else {
      ASS(a.isConjunction());
      AIGRef p1 = a.parent(0);
      AIGRef pp1 = p1.getPositive();
      USharedSet* pp1r = refAtoms.get(pp1);
      AIGRef p2 = a.parent(1);
      AIGRef pp2 = p2.getPositive();
      USharedSet* pp2r = refAtoms.get(pp2);
      if(pp1r && pp2r) {
	ref = pp1r->getUnion(pp2r);
	if(ref->size()>_maxBDDVarCnt) {
	  ref = 0;
	}
      }
      else {
	ref = 0;
      }
//      if(!ref) {
//	if(pp1r && !map.find(pp1)) {
//	  AIGRef pp1Tgt = pp1;
//	  localCompressByBDD(pp1, pp1Tgt);
//	  map.insert(pp1, pp1Tgt);
//	}
//	if(pp2r && !map.find(pp2)) {
//	  AIGRef pp2Tgt = pp2;
//	  localCompressByBDD(pp2, pp2Tgt);
//	  map.insert(pp2, pp2Tgt);
//	}
//      }
      if(ref) {
	ASS(!map.find(a));
	AIGRef cpA = _atr.lev1Deref(a, map);
	AIGRef tgt = cpA;
	localCompressByBDD(cpA, tgt);
	if(a!=tgt) {
	  map.insert(a, tgt);
	}
      }
    }
    ALWAYS(refAtoms.insert(a, ref));
  }

//  AIGRef paig0 = aig0.getPositive();
//  if(paig0.isConjunction() && refAtoms.get(paig0)) {
//    ASS(!map.find(paig0));
//    AIGRef tgt = paig0;
//    localCompressByBDD(paig0, tgt);
//    map.insert(paig0, tgt);
//  }

  _atr.makeIdempotent(map);
  _atr.applyWithCaching(aig0, map);
  AIGRef res = _atr.lev0Deref(aig0, map);

  LOG("pp_aig_compr_attempts","aig compression attempt:"<<endl<<"  src: "<<aig0<<endl<<"  tgt: "<<res);
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

  LOG("pp_aig_compr_all","aig compr: "<<endl
      <<"  src("<<origSz<<"): "<<aig.toString()<<endl
      <<"  tgt("<<comprSz<<"): "<<aCompr.toString());

  if(origSz*_reqFactorDenom>comprSz*_reqFactorNum) {
    LOG("pp_aig_compr_succ","aig compr succeeded: "<<endl<<"  src: "<<aig.toString()<<endl<<"  tgt: "<<aCompr.toString());
    return aCompr;
  }
  else {
    return aig;
  }
}


//////////////////////////////
// AIGCompressingTransformer
//

AIGCompressingTransformer::AIGCompressingTransformer()
 : _compr(_fsh.aig(),5,4)
{
  CALL("AIGCompressingTransformer::AIGCompressingTransformer");
}

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
  Formula* res = _fsh.aigToFormula(simpl);
  LOG("pp_aig_compr_forms","aig compr forms"<<endl<<"  src: "<<(*f)<<endl<<"  tgt: "<<(*res));
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
  if(rhsSimpl->connective()==TRUE) {
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

  res = new FormulaUnit(f, new Inference1(Inference::LOCAL_SIMPLIFICATION, unit), unit->inputType());
  LOG_SIMPL("pp_aig_compr_units",unit,res);

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
  res = new FormulaUnit(fSimpl, new Inference1(Inference::LOCAL_SIMPLIFICATION, unit), unit->inputType());
  LOG_SIMPL("pp_aig_compr_units",unit,res);
  return true;
}

void AIGCompressingTransformer::updateModifiedProblem(Problem& prb)
{
  CALL("AIGCompressingTransformer::updateModifiedProblem");

  prb.invalidateProperty();
}

}
