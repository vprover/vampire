/**
 * @file ProofSimplifier.cpp
 * Implements class ProofSimplifier.
 */

#include "ProofSimplifier.hpp"

namespace Shell
{

ProofSimplifier::ProofSimplifier(UnitSpec refutation)
{
  CALL("ProofSimplifier::ProofSimplifier");

  _refutation = refutation;
  loadProof(refutation, _origProof);
}

void ProofSimplifier::registerTransformation(UnitSpec src, UnitSpec tgt)
{
  CALL("ProofSimplifier::registerTransformation");


}

void ProofSimplifier::loadProof(UnitSpec refutation, Stack<UnitSpec>& tgt)
{
  CALL("ProofSimplifier::loadProof");

  static DHSet<UnitSpec> processed;
  processed.reset();

  static Stack<UnitSpec> stack;
  stack.reset();
  stack.push(refutation);

  while(stack.isNonEmpty()) {
    if(stack.top().isEmpty()) {
      stack.pop();
      ASS(!stack.top().isEmpty());
      UnitSpec proc = stack.pop();
      if(processed.insert(proc)) {
	tgt.push(proc);
      }
    }
    UnitSpec current = stack.top();
    if(processed.find(current)) {
      stack.pop();
      continue;
    }
    stack.push(UnitSpec(0));
    UnitSpecIterator pit = InferenceStore::instance()->getParents(current);
    stack.loadFromIterator(pit);
  }
}



}
