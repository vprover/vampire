/**
 * @file Grounder.hpp
 * Defines class Grounder.
 */

#ifndef __Grounder__
#define __Grounder__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"

namespace Kernel {

using namespace Lib;
using namespace SAT;

class Grounder {
public:
  Grounder();

  SATClauseIterator ground(Clause* cl);
  SATClause* groundNonProp(Clause* cl);
  void groundNonProp(Clause* cl, SATLiteralStack& acc);
  SATLiteral ground(Literal* lit);

  unsigned satVarCnt() const { return _nextSatVar; }

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
  DHMap<Literal*, unsigned> _asgn;
};

class GlobalSubsumptionGrounder : public Grounder {
protected:
  virtual void normalize(unsigned cnt, Literal** lits);
};

class IGGrounder : public Grounder {
protected:
  virtual void normalize(unsigned cnt, Literal** lits);
private:
  class CollapsingApplicator;
  Literal* collapseVars(Literal* lit);
};


}

#endif // __Grounder__
