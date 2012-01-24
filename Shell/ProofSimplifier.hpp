/**
 * @file ProofSimplifier.hpp
 * Defines class ProofSimplifier.
 */

#ifndef __ProofSimplifier__
#define __ProofSimplifier__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/InferenceStore.hpp"
#include "Kernel/Problem.hpp"

#include "AIG.hpp"
#include "AIGInliner.hpp"
#include "AIGCompressor.hpp"

namespace Shell {

using namespace Lib;
using namespace Kernel;

class ProofTransformer {
public:
  ProofTransformer(UnitSpec refutation);
  virtual ~ProofTransformer() {}

  void perform();

  UnitSpec getNewRefutation() {
    CALL("ProofTransformer::getNewRefutation");
    ASS(isRefutation(_newProof.top()));
    return _newProof.top();
  }
protected:
  virtual void preTransform() {}
  virtual UnitSpec transformUnit(UnitSpec u) = 0;

  static bool isRefutation(UnitSpec u);
  static void loadProof(UnitSpec refutation, Stack<UnitSpec>& tgt);

  Stack<UnitSpec> _origProof;
private:

  void derefInference(UnitSpec src, UnitSpec tgt);
  void registerTransformation(UnitSpec src, UnitSpec tgt);

  UnitSpec _refutation;

  DHMap<UnitSpec,UnitSpec> _transformationMap;

  Stack<UnitSpec> _newProof;
};


class ProofSimplifier : public ProofTransformer {
public:
  ProofSimplifier(const Problem& prb, UnitSpec refutation, UnitList* defs);
protected:
  virtual void preTransform();
  virtual UnitSpec transformUnit(UnitSpec u);

private:
  AIGRef getAIG(UnitSpec u);

  const Problem& _prb;
  UnitList* _defs;

  AIGInliner _inl;
  AIG& _aig;
  AIGFormulaSharer& _fsh;
  BDDAIG _bddAig;
};


}

#endif // __ProofSimplifier__
