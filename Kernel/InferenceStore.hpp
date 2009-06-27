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

  struct ClauseSpec
  {
    ClauseSpec() {}
    ClauseSpec(Clause* first, BDDNode* second) : first(first), second(second) {}
    bool operator==(ClauseSpec& o) { return first==o.first && second==o.second; }
    bool operator!=(ClauseSpec& o) { return !(*this==o); }

    Clause* first;
    BDDNode* second;
  };
  static ClauseSpec getClauseSpec(Clause* cl);
  static ClauseSpec getClauseSpec(Clause* cl, BDDNode* prop);

  void recordNonPropInference(Clause* cl);
  void recordNonPropInference(Clause* cl, Inference* inf);
  void recordPropReduce(Clause* cl, BDDNode* oldProp, BDDNode* newProp);
  void recordPropAlter(Clause* cl, BDDNode* oldProp, BDDNode* newProp, Inference::Rule rule);
  void recordMerge(Clause* cl, BDDNode* oldClProp, Clause* addedCl, BDDNode* resultProp);
  void recordMerge(Clause* cl, BDDNode* oldClProp, ClauseSpec* addedCls, int addedClsCnt, BDDNode* resultProp);
  void recordSplitting(Clause* master, BDDNode* oldMasterProp, BDDNode* newMasterProp,
	  unsigned premCnt, Clause** prems);

  void outputProof(ostream& out, Unit* refutation);

private:
  InferenceStore();


  struct FullInference;
  struct ProofPrinter;
  struct TPTPProofCheckPrinter;


  std::string getClauseIdStr(ClauseSpec cs);


  /**
   * A map that for a clause specified by its non-prop. part
   * in Clause object and by prop. part in BDDNode yields an
   * inference that was used to derive this clause.
   *
   * If all premises of a clause have their propositional parts
   * equal to false, and it is the inference with which the
   * Clause object was created, then the inference is not stored
   * here, and the one in clause->inference() is valid.
   *
   * Also clauses with propositional parts equal to true are not
   * being inserted here, as in proofs they're derived by the
   * "tautology introduction" rule that takes no premises.
   */
  DHMap<ClauseSpec, FullInference*, PtrPairSimpleHash> _data;
  DHMultiset<Clause*, PtrIdentityHash> _nextClIds;

  BDD* _bdd;
};

};

#endif /* __InferenceStore__ */
