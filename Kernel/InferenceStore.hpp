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

#include "../Lib/Allocator.hpp"
#include "../Lib/DHMap.hpp"
#include "../Lib/DHMultiset.hpp"
#include "../Lib/Stack.hpp"
#include "../Kernel/BDD.hpp"
#include "../Kernel/Inference.hpp"

namespace Kernel {

using namespace Lib;

class SplittingRecord;

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

  struct UnitSpec
  {
    UnitSpec() {}
    UnitSpec(Unit* f, BDDNode* s) : first(f), second(s) {}
    UnitSpec(Unit* f) : first(f), second(BDD::instance()->getFalse()) {}

    bool operator==(UnitSpec& o) { return first==o.first && second==o.second; }
    bool operator!=(UnitSpec& o) { return !(*this==o); }

    Unit* first;
    BDDNode* second;
  };

  struct FullInference
  {
    FullInference(unsigned premCnt) : csId(0), premCnt(premCnt) { ASS_L(premCnt, 0xFFFF); }

    void* operator new(size_t,unsigned premCnt)
    {
      size_t size=sizeof(FullInference)+premCnt*sizeof(ClauseSpec);
      size-=sizeof(ClauseSpec);

      return ALLOC_KNOWN(size,"InferenceStore::FullInference");
    }

    size_t occupiedBytes()
    {
      size_t size=sizeof(FullInference)+premCnt*sizeof(ClauseSpec);
      size-=sizeof(ClauseSpec);
      return size;
    }

    void increasePremiseRefCounters();

    int csId;
    unsigned premCnt : 16;
    Inference::Rule rule : 16;
    ClauseSpec premises[1];
  };


  //An ugly hack, done just to get it working a few days before CASC deadline:)
  class SplittingRecord
  {
  public:
    SplittingRecord(Clause* splittedClause) : namedComps(1), premise(getClauseSpec(splittedClause)) {}

    Stack<pair<int,Clause*> > namedComps;
    ClauseSpec premise;
    ClauseSpec result;


    CLASS_NAME("InferenceStore::SplittingRecord");
    USE_ALLOCATOR(SplittingRecord);
  };

  static ClauseSpec getClauseSpec(Clause* cl);
  static ClauseSpec getClauseSpec(Clause* cl, BDDNode* prop);

  void recordNonPropInference(Clause* cl);
  void recordNonPropInference(Clause* cl, Inference* inf);
  void recordPropReduce(Clause* cl, BDDNode* oldProp, BDDNode* newProp);
  void recordPropAlter(Clause* cl, BDDNode* oldProp, BDDNode* newProp, Inference::Rule rule);
  void recordMerge(Clause* cl, BDDNode* oldClProp, Clause* addedCl, BDDNode* resultProp);
  void recordMerge(Clause* cl, BDDNode* oldProp, BDDNode* addedProp, BDDNode* resultProp);
  void recordMerge(Clause* cl, BDDNode* oldClProp, ClauseSpec* addedCls, int addedClsCnt, BDDNode* resultProp);
  void recordSplitting(SplittingRecord* srec, unsigned premCnt, Clause** prems);

  void outputProof(ostream& out, Unit* refutation);

  VirtualIterator<ClauseSpec> getParents(Clause* cl);
  VirtualIterator<UnitSpec> getUnitParents(Unit* u, BDDNode* prop);

  void deleteClauseRecords(Clause* cl);

  std::string getClauseIdStr(ClauseSpec cs);
  std::string getClauseIdSuffix(ClauseSpec cs);

  bool findInference(ClauseSpec cs, FullInference*& finf)
  {
    return _data.find(cs,finf);
  }

  bool findSplitting(ClauseSpec cs, SplittingRecord*& srec)
  {
    return _splittingRecords.find(cs,srec);
  }


private:
  InferenceStore();

  struct ProofPrinter;
  struct TPTPProofCheckPrinter;
  struct LatexProofPrinter;




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

  DHMap<ClauseSpec, SplittingRecord*, PtrPairSimpleHash> _splittingRecords;

  BDD* _bdd;
};


};

#endif /* __InferenceStore__ */
