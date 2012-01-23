/**
 * @file ProofSimplifier.hpp
 * Defines class ProofSimplifier.
 */

#ifndef __ProofSimplifier__
#define __ProofSimplifier__

#include "Forwards.hpp"

#include "Lib/Stack.hpp"
#include "Kernel/InferenceStore.hpp"


namespace Shell {

using namespace Lib;
using namespace Kernel;

class ProofSimplifier {
public:
  ProofSimplifier(UnitSpec refutation);

  static void loadProof(UnitSpec refutation, Stack<UnitSpec>& tgt);
private:
  UnitSpec _refutation;

  Stack<UnitSpec> _origProof;
  Stack<UnitSpec> _newProof;

};

}

#endif // __ProofSimplifier__
