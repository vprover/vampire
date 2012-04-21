/**
 * @file EquivalenceDiscoverer.hpp
 * Defines class EquivalenceDiscoverer.
 */

#ifndef __EquivalenceDiscoverer__
#define __EquivalenceDiscoverer__

#include "Forwards.hpp"

#include "Lib/ArrayMap.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/FreshnessGuard.hpp"
#include "Lib/Stack.hpp"
#include "Lib/ScopedPtr.hpp"

#include "Kernel/Grounder.hpp"
#include "Kernel/Problem.hpp"

#include "SAT/SATLiteral.hpp"
#include "SAT/SATSolver.hpp"

#include "AIGDefinitionIntroducer.hpp"
#include "Options.hpp"
#include "Preprocess.hpp"



namespace Shell {

using namespace Lib;
using namespace Kernel;
using namespace SAT;

class EquivalenceDiscoverer {
public:
  enum CandidateRestriction {
    CR_NONE,
    CR_DEFINITIONS,
    CR_EQUIVALENCES
  };
private:

  //options
  unsigned _satConflictCountLimit;
  CandidateRestriction _restriction;
  bool _discoverImplications;

  /** A getEquivalences function can be called only once on the object.
   * This object enforces this restriction. */
  FreshnessGuard _fresh;

  bool _restrictedRange;
  DHSet<Literal*> _restrictedRangeSet1;
  DHSet<Literal*> _restrictedRangeSet2;

  GlobalSubsumptionGrounder _gnd;
  ScopedPtr<SATSolver> _solver;
  ScopedPtr<SATSolver> _proofRecordingSolver;

  SATLiteralStack _eligibleSatLits;

//  DHMap<Literal*,SATLiteral> _f2s;
  DHMap<SATLiteral,Literal*> _s2f;

  unsigned _maxSatVar;

  SATClauseStack _satClauses;
  SATClauseStack _filteredSatClauses;

  Literal* getFOLit(SATLiteral slit) const;

  SATSolver& getProofRecordingSolver();
  void getImplicationPremises(SATLiteral l1, SATLiteral l2, Stack<UnitSpec>& acc);
  Inference* getInference(SATLiteral l1, SATLiteral l2, bool equivalence);

  void addGrounding(Clause* cl);
  void collectRelevantLits();

  bool isEligible(Literal* l);
  bool isEligiblePair(Literal* l1, Literal* l2);

  bool handleTrueLiteral(SATLiteral l, UnitList*& eqAcc);
  bool handleEquivalence(SATLiteral l1, SATLiteral l2, UnitList*& eqAcc);
  bool handleImplication(SATLiteral lhs, SATLiteral rhs, UnitList*& eqAcc);

  void doISSatDiscovery(UnitList*& res);

  static int satLiteralVar(SATLiteral l) { return l.var(); }
public:
  EquivalenceDiscoverer(bool normalizeForSAT, unsigned satConflictCountLimit,
      CandidateRestriction restriction, bool discoverImplications);

  void setRestrictedRange(LiteralIterator set1, LiteralIterator set2);

  UnitList* getEquivalences(ClauseIterator clauses);
  UnitList* getEquivalences(UnitList* units, const Options* opts=0);
};

class FormulaEquivalenceDiscoverer
{
public:
  FormulaEquivalenceDiscoverer(EquivalenceDiscoverer& ed) : _adi(1), _ed(ed) {}

  UnitList* getEquivalences(UnitList* units, const Options* opts=0);

private:

  UnitList* collectOuterEquivalences(UnitList* namedEqs);
  Formula* inner2Outer(Formula* f, UnitStack& premAcc);

  FreshnessGuard _fresh;
  AIGDefinitionIntroducer _adi;
  EquivalenceDiscoverer& _ed;
};

class EquivalenceDiscoveringTransformer {
public:
  EquivalenceDiscoveringTransformer(const Options& opts);

  bool apply(Problem& prb);
  bool apply(UnitList*& units);
private:
  const Options& _opts;
};

}

#endif // __EquivalenceDiscoverer__
