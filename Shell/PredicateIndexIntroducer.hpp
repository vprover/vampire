/**
 * @file PredicateIndexIntroducer.hpp
 * Defines class PredicateIndexIntroducer.
 */

#ifndef __PredicateIndexIntroducer__
#define __PredicateIndexIntroducer__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/SharedSet.hpp"

#include "Kernel/FormulaTransformer.hpp"



namespace Shell {

using namespace Lib;
using namespace Kernel;

class PredicateIndexIntroducer : public ScanAndApplyLiteralTransformer {
public:
  PredicateIndexIntroducer();

  virtual void scan(UnitList* units);

  using ScanAndApplyLiteralTransformer::apply;

protected:
  virtual Literal* apply(Literal* lit, UnitStack& premAcc);

  virtual void updateModifiedProblem(Problem& prb);
private:
  // scanning to determine what to index

  typedef const SharedSet<unsigned> DistGrpSet;

  struct ArgOccInfo {
    ArgOccInfo() : _new(true) {}

    void scanArg(PredicateIndexIntroducer& parent, TermList t);

    bool _new;
    bool _eligible;
    DistGrpSet* _distGrps;
    Term* _onlyOcc;
  };

  void scan(Literal* lit);
  DistGrpSet* getDistGrps(TermList trm);

  /** if true, symbols starting with "$$" are considered to be distinct from each other */
  bool _assumeSSDistinctGroup;
  unsigned _ssDistinctGroupID;

  DHSet<Literal*> _seen;
  /** pair (predicate number,argument index) refering to an argument of a predicate */
  typedef pair<unsigned,unsigned> ArgId;
  typedef DHMap<ArgId,ArgOccInfo> ArgOccInfoMap;
  ArgOccInfoMap _predArgOccInfos;

  typedef DHMap<unsigned,Stack<unsigned> > IdxPredArgsMap;
  IdxPredArgsMap _indexedPredArgs;


private:
  //replacing atoms by indexed ones

  unsigned getIndexedPred(Literal* lit);

  /** Key to the indexed predicate map */
  typedef pair<unsigned,TermStack> IdxPredKey;
  DHMap<IdxPredKey,unsigned> _idxPreds;
};

}

#endif // __PredicateIndexIntroducer__
