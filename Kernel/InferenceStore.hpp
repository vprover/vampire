/**
 * @file InferenceStore.hpp
 * Defines class InferenceStore.
 */


#ifndef __InferenceStore__
#define __InferenceStore__

#include <utility>
#include <ostream>
#include <string>

#include "Forwards.hpp"

#include "Lib/Allocator.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/DHMultiset.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/BDD.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"

namespace Kernel {

using namespace Lib;

class SplittingRecord;

class InferenceStore
{
public:
  static InferenceStore* instance();

  struct UnitSpec
  {
    UnitSpec() {}
    UnitSpec(Unit* u, bool ignoreProp) : _unit(u)
    {
      if(!ignoreProp && u->isClause() && static_cast<Clause*>(u)->prop()) {
	_prop=static_cast<Clause*>(u)->prop();
      }
      else {
	_prop=BDD::instance()->getFalse();
      }
    }
    UnitSpec(Unit* u, BDDNode* prop) : _unit(u), _prop(prop) {}
    bool operator==(UnitSpec& o) { return _unit==o._unit && _prop==o._prop; }
    bool operator!=(UnitSpec& o) { return !(*this==o); }

    static unsigned hash(const UnitSpec& o)
    {
      return PtrPairSimpleHash::hash(make_pair(o._unit, o._prop));
    }

    bool isClause() const { return _unit->isClause(); }
    bool isPropTautology() const { return BDD::instance()->isTrue(_prop); }

    Clause* cl() const
    {
      ASS(_unit->isClause());
      return static_cast<Clause*>(_unit);
    }
    Unit* unit() const { return _unit; }
    BDDNode* prop() const { return _prop; }

  private:
    Unit* _unit;
    BDDNode* _prop;
  };

  typedef VirtualIterator<UnitSpec> UnitSpecIterator;

  struct FullInference
  {
    FullInference(unsigned premCnt) : csId(0), premCnt(premCnt) { }

    void* operator new(size_t,unsigned premCnt)
    {
      size_t size=sizeof(FullInference)+premCnt*sizeof(UnitSpec);
      size-=sizeof(UnitSpec);

      return ALLOC_KNOWN(size,"InferenceStore::FullInference");
    }

    size_t occupiedBytes()
    {
      size_t size=sizeof(FullInference)+premCnt*sizeof(UnitSpec);
      size-=sizeof(UnitSpec);
      return size;
    }

    void increasePremiseRefCounters();

    int csId;
    unsigned premCnt;
    Inference::Rule rule;
    UnitSpec premises[1];
  };


  //An ugly hack, done just to get it working a few days before CASC deadline:)
  class SplittingRecord
  {
  public:
    SplittingRecord(Clause* splittedClause) : namedComps(1), premise(getClauseSpec(splittedClause)) {}

    Stack<pair<int,Clause*> > namedComps;
    UnitSpec premise;
    UnitSpec result;


    CLASS_NAME("InferenceStore::SplittingRecord");
    USE_ALLOCATOR(SplittingRecord);
  };

  static UnitSpec getClauseSpec(Clause* cl);
  static UnitSpec getClauseSpec(Clause* cl, BDDNode* prop);

  void recordNonPropInference(Clause* cl);
  void recordNonPropInference(Clause* cl, Inference* inf);
  void recordPropReduce(Clause* cl, BDDNode* oldProp, BDDNode* newProp);
  void recordPropAlter(Clause* cl, BDDNode* oldProp, BDDNode* newProp, Inference::Rule rule);
  void recordMerge(Clause* cl, BDDNode* oldClProp, Clause* addedCl, BDDNode* resultProp);
  void recordMerge(Clause* cl, BDDNode* oldProp, BDDNode* addedProp, BDDNode* resultProp);
  void recordMerge(Clause* cl, BDDNode* oldClProp, UnitSpec* addedCls, int addedClsCnt, BDDNode* resultProp);
  void recordSplitting(SplittingRecord* srec, unsigned premCnt, Clause** prems);

  void outputProof(ostream& out, Unit* refutation);

  UnitSpecIterator getParents(UnitSpec us, Inference::Rule& rule);
  UnitSpecIterator getParents(UnitSpec us);

  void deleteClauseRecords(Clause* cl);

  std::string getUnitIdStr(UnitSpec cs);
  std::string getClauseIdSuffix(UnitSpec cs);

  bool findInference(UnitSpec cs, FullInference*& finf)
  {
    return _data.find(cs,finf);
  }

  bool findSplitting(UnitSpec cs, SplittingRecord*& srec)
  {
    return _splittingRecords.find(cs,srec);
  }


private:
  InferenceStore();

  struct ProofPrinter;
  struct TPTPProofPrinter;
  struct ProofCheckPrinter;

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
  DHMap<UnitSpec, FullInference*, UnitSpec> _data;
  DHMultiset<Clause*, PtrIdentityHash> _nextClIds;

  DHMap<UnitSpec, SplittingRecord*, UnitSpec> _splittingRecords;

  BDD* _bdd;
};


};

#endif /* __InferenceStore__ */
