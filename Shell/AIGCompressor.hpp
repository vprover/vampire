/**
 * @file AIGCompressor.hpp
 * Defines class AIGCompressor.
 */

#ifndef __AIGCompressor__
#define __AIGCompressor__

#include "Forwards.hpp"

#include "Lib/SharedSet.hpp"

#include "Kernel/BDD.hpp"

#include "AIG.hpp"

namespace Kernel {
class InterpretedLiteralEvaluator;
}

namespace Shell {

using namespace Lib;
using namespace Kernel;

class BDDAIG {
public:
  BDDAIG(AIG& aig) : _nextVar(1), _bdd(BDD::instance()), _aig(aig) {};

  void loadBDDAssignmentFromProblem(const Problem& prb);

  /**
   * Convert AIGRef into a BDD.
   * Quantifier AIG nodes will be treated as atoms.
   */
  BDDNode* a2b(AIGRef a);
  AIGRef b2a(BDDNode* b);
  void reset();
private:
  struct A2BConjBuildingTask;
  struct B2ATask;

  BDDNode* bddFromAIGConj(AIGRef node, BDDNode* c1, BDDNode* c2);
  bool attemptLocalA2B(AIGRef a, BDDNode*& res);
  bool attemptLocalA2BOrAddTask(AIGRef a, BDDNode** resTgt, Stack<A2BConjBuildingTask*>& taskStack);

  AIGRef aigFromCompoundBDD(BDDNode* b, AIGRef tAig, AIGRef fAig);
  bool attemptLocalB2A(BDDNode* b, AIGRef& res);
  bool attemptLocalB2AOrAddTask(BDDNode* b, AIGRef* resTgt, Stack<B2ATask*>& taskStack);
  AIGRef naiveB2A(BDDNode* b);


  unsigned _nextVar;

  DHMap<AIGRef, BDDNode*> _a2bCache;
  DHMap<BDDNode*, AIGRef> _b2aCache;
  DHMap<unsigned, AIGRef> _varAtoms;

  BDD* _bdd;
  AIG& _aig;
};

class AIGCompressor {
public:
  typedef AIGTransformer::RefMap RefMap;

  AIGCompressor(AIG& aig, unsigned reqFactorNum=1, unsigned reqFactorDenom=1, unsigned maxBddVarCnt=16);
  ~AIGCompressor();

  AIGRef compress(AIGRef aig);
  AIGRef compressByBDD(AIGRef aig);

  void populateBDDCompressingMap(AIGInsideOutPosIterator& aigIt, AIGTransformer::RefMap& map);

private:
  AIGRef tryCompressAtom(AIGRef atom);


  bool tryCompareAIGGoodness(AIGRef a1, AIGRef a2, Comparison& res);
  bool doHistoryLookUp(AIGRef aig, BDDNode* bdd, AIGRef& tgt);
  void doLookUpImprovement(AIGTransformer::RefMap& mapToFix);

  bool localCompressByBDD(AIGRef aig, AIGRef& tgt, bool historyLookUp, bool& usedLookUp);
  AIGRef attemptCompressByBDD(AIGRef aig);

  DHMap<AIGRef, size_t> _aigDagSizeCache;

  size_t getAIGDagSize(AIGRef aig);


  typedef const SharedSet<unsigned> USharedSet;
  /**
   * Map that assigns AIG nodes a set of nodes they contain that are unsplittable
   * for the purpose of conversion to BDDs.
   */
  typedef DHMap<AIGRef,USharedSet*> UnsplittableSetMap;
  USharedSet* conjGetUnsplittableSet(USharedSet* p1set, USharedSet* p2set);
  bool tryGetUnsplittableSetLocally(AIGRef a, UnsplittableSetMap& cache, USharedSet*& res, bool doOneUnfolding);
  USharedSet* getUnsplittableSet(AIGRef a, UnsplittableSetMap& cache);



  /** Maximal number of BDD variables we want to use (to stay safe from blow-up) */
  unsigned _maxBDDVarCnt;
  unsigned _reqFactorNum;
  unsigned _reqFactorDenom;


  typedef DHMap<BDDNode*,AIGRef> LookUpMap;
  /** If BDD didn't compress an AIG, we store the AIG here,
   * so next time we see the same BDD, we know there is something
   * equivalent to it */
  LookUpMap _lookUp;
  /** If we have found a better AIG for AIG present in the _lookUp map */
  RefMap _lookUpImprovement;
  bool _lookUpNeedsImprovement;

  AIG& _aig;
  AIGTransformer _atr;
  BDDAIG _ba;

  InterpretedLiteralEvaluator* _ilEval;
};

class AIGCompressingTransformer : public ScanAndApplyFormulaUnitTransformer {
public:
  AIGCompressingTransformer(unsigned maxBddVarCnt=16);

  using ScanAndApplyFormulaUnitTransformer::apply;
  Formula* apply(Formula* f);
  bool applyToDefinition(FormulaUnit* unit, Unit*& res);
  virtual bool apply(FormulaUnit* unit, Unit*& res);

protected:
  virtual void updateModifiedProblem(Problem& prb);

private:
  AIGFormulaSharer _fsh;
  AIGCompressor _compr;
};

}

#endif // __AIGCompressor__
