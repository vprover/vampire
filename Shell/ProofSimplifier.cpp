/**
 * @file ProofSimplifier.cpp
 * Implements class ProofSimplifier.
 */

#include "ProofSimplifier.hpp"

namespace Shell
{

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
      tgt.push(stack.pop());
    }
    UnitSpec current = stack.top();
    UnitSpecIterator pit = InferenceStore::instance()->getParents(current);
    NOT_IMPLEMENTED;
  }
}

}
