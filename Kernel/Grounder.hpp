/**
 * @file Grounder.hpp
 * Defines class Grounder.
 */

#ifndef __Grounder__
#define __Grounder__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/ScopedPtr.hpp"
#include "Lib/SmartPtr.hpp"

#include "Kernel/Term.hpp"

#include "SAT/SAT2FO.hpp"

namespace Kernel {

using namespace Lib;
using namespace SAT;

class Grounder {
public:
  CLASS_NAME(Grounder);
  USE_ALLOCATOR(Grounder);
  
  Grounder() : _nextSatVar(1), _sat2fo(0), _satSolver(0) {}
  Grounder(SATSolver* satSolver) : _nextSatVar(1), _sat2fo(0), _satSolver(satSolver) {}
  virtual ~Grounder() { CALL("Kernel::~Grounder"); }
  void useSAT2FO(SAT2FO& sat2fo){ _sat2fo = &sat2fo;}

  SATClauseIterator ground(Clause* cl,bool use_n,bool ignore_splits=true);
  SATClause* groundNonProp(Clause* cl, bool use_n, Literal** normLits=0);
  void groundNonProp(Clause* cl, SATLiteralStack& acc, bool use_n, Literal** normLits=0);
  SATLiteral ground(Literal* lit,bool use_n);

  unsigned satVarCnt() const { if(_sat2fo){ return 1+_sat2fo->maxSATVar();} return _nextSatVar; }

  static void recordInference(Clause* origClause, SATClause* refutation, Clause* resultClause);

  LiteralIterator groundedLits();

protected:
  /**
   * Normalize literals before grounding.
   *
   * The order of literals in @c lits must be preserved.
   */
  virtual void normalize(unsigned cnt, Literal** lits) = 0;

private:
  SATLiteral groundNormalized(Literal*);


  unsigned _nextSatVar;
  SAT2FO* _sat2fo;

  /** Map from positive literals to SAT variable numbers */
  DHMap<Literal*, unsigned> _asgn;
  /** Used to communicate source literals, should be 0 unless this is IGGrounded */
  // IGAlgorithm will delete this
  SATSolver* _satSolver;
};

class GlobalSubsumptionGrounder : public Grounder {
  struct OrderNormalizingComparator;

  bool _doNormalization;
public:
  CLASS_NAME(GlobalSubsumptionGrounder);
  USE_ALLOCATOR(GlobalSubsumptionGrounder);

  GlobalSubsumptionGrounder(bool doNormalization=true) : _doNormalization(doNormalization) {}
protected:
  virtual void normalize(unsigned cnt, Literal** lits);
};

class IGGrounder : public Grounder {
public:
  CLASS_NAME(IGGrounder);
  USE_ALLOCATOR(IGGrounder);

  IGGrounder(SATSolver* satSolver);
private:
  TermList _tgtTerm;
protected:
  virtual void normalize(unsigned cnt, Literal** lits);
private:
  class CollapsingApplicator;
  Literal* collapseVars(Literal* lit);
};


}

#endif // __Grounder__
