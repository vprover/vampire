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

class InferenceStore
{
public:

  static InferenceStore* instance();

  void recordNonPropInference(Clause* cl);
  void recordPropReduce(Clause* cl, BDDNode* oldProp, BDDNode* newProp);
  void recordPropAlter(Clause* cl, BDDNode* oldProp, BDDNode* newProp, Inference::Rule rule);
  void recordMerge(Clause* cl, BDDNode* oldClProp, Clause* addedCl, BDDNode* resultProp);
  void recordSplitting(Clause* master, BDDNode* oldMasterProp, BDDNode* newMasterProp,
	  unsigned premCnt, Clause** prems);
private:
  typedef pair<Clause*, BDDNode*> ClauseSpec;

  struct FullInference;
  ClauseSpec getClauseSpec(Clause* cl);
  ClauseSpec getClauseSpec(Clause* cl, BDDNode* prop);


  DHMap<ClauseSpec, FullInference*, PtrPairSimpleHash> _data;
};

};

#endif /* __InferenceStore__ */
