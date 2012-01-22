/**
 * @file EquivalenceDiscoverer.hpp
 * Defines class EquivalenceDiscoverer.
 */

#ifndef __EquivalenceDiscoverer__
#define __EquivalenceDiscoverer__

#include "Forwards.hpp"

#include "Lib/ArrayMap.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/Stack.hpp"
#include "Lib/ScopedPtr.hpp"

#include "Kernel/Grounder.hpp"
#include "Kernel/Problem.hpp"

#include "SAT/SATLiteral.hpp"

#include "Options.hpp"
#include "Preprocess.hpp"



namespace Shell {

using namespace Lib;
using namespace Kernel;
using namespace SAT;

class EquivalenceDiscoverer {

  //options
  unsigned _satConflictCountLimit;
  bool _checkOnlyDefinitionHeads;

  GlobalSubsumptionGrounder _gnd;
  TWLSolver* _solver;

  SATLiteralStack _eligibleSatLits;
//  LiteralStack _foLits;

//  DHMap<Literal*,SATLiteral> _f2s;
  DHMap<SATLiteral,Literal*> _s2f;

  /**
   * Contains values of initial assignment.
   * If variable isn't in the map, it was assigned a don't care.
   */
  ArrayMap<bool> _initialAssignment;

  unsigned _maxSatVar;


  SATClauseStack _satClauses;
  SATClauseStack _filteredSatClauses;

  Literal* getFOLit(SATLiteral slit) const;

  void addGrounding(Clause* cl);
  void collectRelevantLits();

  bool isEligible(Literal* l);

  void loadInitialAssignment();

  bool areEquivalent(SATLiteral l1, SATLiteral l2);

  bool handleEquivalence(SATLiteral l1, SATLiteral l2, UnitList*& eqAcc);
public:
  EquivalenceDiscoverer(bool normalizeForSAT, unsigned satConflictCountLimit, bool checkOnlyDefinitionHeads);
  ~EquivalenceDiscoverer();

  UnitList* getEquivalences(ClauseIterator clauses);
  UnitList* getEquivalences(UnitList* units, const Options* opts=0);
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
