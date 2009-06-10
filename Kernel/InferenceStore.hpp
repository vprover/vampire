/**
 * @file InferenceStore.hpp
 * Defines class InferenceStore.
 */


#ifndef __InferenceStore__
#define __InferenceStore__

#include <utility>
#include <ostream>
#include <string>

#include "../Forwards.hpp"

#include "../Lib/DHMap.hpp"
#include "../Lib/DHMultiset.hpp"
#include "../Kernel/Inference.hpp"

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

  void outputProof(ostream& out, Unit* refutation);
private:
  struct ClauseSpec
  {
    ClauseSpec() {}
    ClauseSpec(Clause* first, BDDNode* second) : first(first), second(second) {}
    bool operator==(ClauseSpec& o) { return first==o.first && second==o.second; }
    bool operator!=(ClauseSpec& o) { return !(*this==o); }

    Clause* first;
    BDDNode* second;
  };

  struct FullInference;
  struct ProofPrinter;
  struct TPTPProofCheckPrinter;

  static ClauseSpec getClauseSpec(Clause* cl);
  static ClauseSpec getClauseSpec(Clause* cl, BDDNode* prop);

  int getClauseSpecId(ClauseSpec cs);


  DHMap<ClauseSpec, FullInference*, PtrPairSimpleHash> _data;
  DHMultiset<Clause*, PtrIdentityHash> _nextClIds;
};

};

#endif /* __InferenceStore__ */
