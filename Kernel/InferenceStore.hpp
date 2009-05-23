/**
 * @file InferenceStore.hpp
 * Defines class InferenceStore.
 */


#ifndef __InferenceStore__
#define __InferenceStore__

#include <utility>

#include "../Forwards.hpp"

#include "../Lib/DHMap.hpp"
#include "../Kernel/BDD.hpp"

namespace Kernel {

using namespace Lib;

class FullInference
{
  enum Type
  {
    MERGE=201,
    SPLITTING=202,
    SUBSUMPTION_SUBTRACTION=203

  };
};

class InferenceStore
{
public:

  void recordNonPropInference(Clause* cl);
  void recordInference(Clause* cl, FullInference* inf);
private:
  typedef pair<Clause*, BDDNode*> ClauseSpec;
  DHMap<ClauseSpec, Inference*, PtrPairSimpleHash> _data;
};

};

#endif /* __InferenceStore__ */
