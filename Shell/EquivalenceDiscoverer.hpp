/**
 * @file EquivalenceDiscoverer.hpp
 * Defines class EquivalenceDiscoverer.
 */

#ifndef __EquivalenceDiscoverer__
#define __EquivalenceDiscoverer__

#include "Forwards.hpp"

#include "Lib/DHSet.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/Grounder.hpp"

#include "SAT/SATLiteral.hpp"
#include "SAT/SATSolver.hpp"



namespace Shell {

using namespace Lib;
using namespace Kernel;
using namespace SAT;

class EquivalenceDiscoverer {
  bool _onlyPropEqCheck;

  GlobalSubsumptionGrounder _gnd;
  SATSolverSCP _solver;

  SATLiteralStack _eligibleSatLits;
//  LiteralStack _foLits;

//  DHMap<Literal*,SATLiteral> _f2s;
  DHMap<SATLiteral,Literal*> _s2f;

  unsigned _maxSatVar;


  SATClauseStack _satClauses;
  SATClauseStack _filteredSatClauses;

  void addGrounding(Clause* cl);
  void collectRelevantLits();

  bool isEligible(Literal* l);

  bool areEquivalent(SATLiteral l1, SATLiteral l2);

  void handleEquivalence(SATLiteral l1, SATLiteral l2, UnitList*& eqAcc);
public:
  EquivalenceDiscoverer(bool normalizeForSAT, bool onlyPropEqCheck);

  UnitList* getEquivalences(ClauseIterator clauses);
};

}

#endif // __EquivalenceDiscoverer__
