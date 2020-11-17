
/*
 * File ProofSimplifier.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file ProofSimplifier.cpp
 * Implements class ProofSimplifier.
 */

#include "Kernel/Clause.hpp"
#include "Kernel/ColorHelper.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"

#include "Flattening.hpp"

#include "ProofSimplifier.hpp"

#define DEBUG_SURPRISING_COLORS 0

namespace Shell
{

ProofTransformer::ProofTransformer(Unit* refutation)
{
  CALL("ProofTransformer::ProofTransformer");

  _refutation = refutation;
}

void ProofTransformer::perform()
{
  CALL("ProofTransformer::perform");

  loadProof(_refutation, _origProof);

  preTransform();

  Stack<Unit*>::BottomFirstIterator prIt(_origProof);
  while(prIt.hasNext()) {
    Unit* u = prIt.next();
    Unit* tgt = transformUnit(u);
    registerTransformation(u, tgt);
    if(tgt != 0) {
      derefInference(u, tgt);
      _newProof.push(tgt);
      //maybe we've simplified some unit into a refutation earlier...
      if(isRefutation(tgt)) {
	break;
      }
    }
  }
}

void ProofTransformer::registerTransformation(Unit* src, Unit* tgt)
{
  CALL("ProofTransformer::registerTransformation");
  ASS_NEQ(src,0);
  ALWAYS(_transformationMap.insert(src, tgt));
}

/**
 * Take the inference of src, transform the premises and assign it to tgt
 *
 * Parents of src must have been already processed and their transformation registered.
 */
void ProofTransformer::derefInference(Unit* src, Unit* tgt)
{
  CALL("derefInference");

  InferenceStore* inf = InferenceStore::instance();

  static Stack<Unit*> tgtPrems;
  tgtPrems.reset();

#if DEBUG_INFERENCE_COLORS
  Color srcClr = src.unit()->getColor();
  Color tgtClr = tgt.unit()->getColor();
  Color srcParClr = COLOR_TRANSPARENT;
  Color tgtParClr = COLOR_TRANSPARENT;
#endif
  Inference::Rule rule;
  UnitIterator pit = inf->getParents(src, rule);
  while(pit.hasNext()) {
    Unit* srcPar = pit.next();

#if DEBUG_INFERENCE_COLORS
    srcParClr = ColorHelper::combine(srcParClr, srcPar.unit()->getColor());
#endif

    Unit* tgtPar = _transformationMap.get(srcPar);
    if(tgtPar != 0) {
#if DEBUG_INFERENCE_COLORS
      tgtParClr = ColorHelper::combine(tgtParClr, tgtPar.unit()->getColor());
#endif
      tgtPrems.push(tgtPar);
    }
  }

#if DEBUG_INFERENCE_COLORS
  if(!tgtPrems.isEmpty()) {
    ASS(srcParClr!=COLOR_INVALID);
    ASS(tgtParClr!=COLOR_INVALID);
    ASS(srcClr!=COLOR_INVALID);
    ASS(tgtClr!=COLOR_INVALID);

    ASS(srcParClr!=COLOR_TRANSPARENT  || srcClr==COLOR_TRANSPARENT);
    ASS(tgtParClr!=COLOR_TRANSPARENT  || tgtClr==COLOR_TRANSPARENT);
  }
#endif


  unsigned premCnt = tgtPrems.size();
  InferenceStore::FullInference* finf = new(premCnt) InferenceStore::FullInference(premCnt);
  finf->rule = rule;
  for(unsigned i=0; i<premCnt; i++) {
    finf->premises[i] = tgtPrems[i];
  }
  inf->recordInference(tgt, finf);
}

bool ProofTransformer::isRefutation(Unit* u)
{
  CALL("ProofTransformer::isRefutation");
  ASS_NEQ(u,0);

  if(u->isClause()) { return u->asClause()->isEmpty(); }
  FormulaUnit* fu = static_cast<FormulaUnit*>(u);
  return fu->formula()->connective()==FALSE;
}

void ProofTransformer::loadProof(Unit* refutation, Stack<Unit*>& tgt)
{
  CALL("ProofTransformer::loadProof");

  static DHSet<Unit*> processed;
  processed.reset();

  static Stack<Unit*> stack;
  stack.reset();
  stack.push(refutation);

  while(stack.isNonEmpty()) {
    if(stack.top() == 0) {
      stack.pop();
      ASS(stack.top() != 0);
      Unit* proc = stack.pop();
      if(processed.insert(proc)) {
	tgt.push(proc);
      }
      continue;
    }
    Unit* current = stack.top();
    ASS(current != 0);
    if(processed.find(current)) {
      stack.pop();
      continue;
    }
    stack.push(0);
    UnitIterator pit = InferenceStore::instance()->getParents(current);
    stack.loadFromIterator(pit);
  }
}

///////////////////////
// ProofSimplifier
//

ProofSimplifier::ProofSimplifier(const Problem& prb, Unit* refutation, UnitList* defs)
 : ProofTransformer(refutation), /*_prb(prb), MS: unused */ _defs(defs), _aig(_inl.aig()), _fsh(_inl.fsh()), _bddAig(_aig)
{
  _bddAig.loadBDDAssignmentFromProblem(prb);
}

AIGRef ProofSimplifier::getAIG(Unit* u)
{
  CALL("ProofSimplifier::getAIG");

  //AIGRef bddA = _bddAig.b2a(u.prop());

  AIGRef formA;
  if(u->isClause()) {
    formA = _fsh.getAIG(u->asClause());
  }
  else {
    FormulaUnit* fu = static_cast<FormulaUnit*>(u);
    formA = _fsh.apply(fu->formula()).second;
  }

  AIGRef a = formA; //_aig.getDisj(bddA, formA);
  return a;
}

void ProofSimplifier::preTransform()
{
  CALL("ProofSimplifier::preTransform");

  Stack<Unit*>::BottomFirstIterator pit(_origProof);
  while(pit.hasNext()) {
    Unit* u = pit.next();
    AIGRef a = getAIG(u);
    _inl.addRelevant(a);
  }
  _inl.scan(_defs);
}

Unit* ProofSimplifier::transformUnit(Unit* u)
{
  CALL("ProofSimplifier::transformUnit");

  AIGRef a = getAIG(u);

  AIGInliner::PremSet* prems;
  AIGRef simplA = _inl.apply(a, prems);
  if(simplA.isTrue()) {
    return 0;
  }
  Formula* form = _fsh.aigToFormula(simplA);
  form = Flattening::flatten(form);
  FormulaUnit* res = new FormulaUnit(form, new Inference0(Inference::TAUTOLOGY_INTRODUCTION), u->inputType());
  return res;
}

}
