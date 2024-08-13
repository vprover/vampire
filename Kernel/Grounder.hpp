/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
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

namespace Kernel {

using namespace SAT;

class Grounder {
public:
  Grounder(SATSolver* satSolver) : _satSolver(satSolver) {}
  virtual ~Grounder() {}

  // TODO: sort out the intended semantics and the names of these four beasts:
  SATLiteral groundLiteral(Literal* lit);
  SATClause* ground(Clause* cl);
  SATClause* groundNonProp(Clause* cl, Literal** normLits=0);
  void groundNonProp(Clause* cl, SATLiteralStack& acc, Literal** normLits=0);

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

  /** Map from positive literals to SAT variable numbers */
  Lib::DHMap<Literal*, unsigned> _asgn;
  
  /** Pointer to a SATSolver instance for which the grounded clauses
   * are being prepared. Used to request new variables from the Solver.
   *
   * Also used to communicate source literals with IGGrounder. */
  SATSolver* _satSolver;
};

class GlobalSubsumptionGrounder : public Grounder {
  struct OrderNormalizingComparator;

  bool _doNormalization;
public:
  GlobalSubsumptionGrounder(SATSolver* satSolver, bool doNormalization=true) 
          : Grounder(satSolver), _doNormalization(doNormalization) {}
protected:
  virtual void normalize(unsigned cnt, Literal** lits);
};

class IGGrounder : public Grounder {
public:
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
