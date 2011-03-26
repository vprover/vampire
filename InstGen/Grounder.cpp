/**
 * @file Grounder.cpp
 * Implements class Grounder.
 */

#include "Kernel/Clause.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Term.hpp"

#include "SAT/SATClause.hpp"
#include "SAT/SATLiteral.hpp"

#include "Grounder.hpp"

namespace InstGen
{
using namespace Kernel;

Grounder::Grounder()
: _nextSatVar(1)
{
  CALL("Grounder::Grounder");

}

/**
 * Return SATClause that is a result of grounding of @c cl.
 *
 * Corresponding literals are at corresponding positions.
 */
SATClause* Grounder::ground(Clause* cl)
{
  CALL("Grounder::ground(Clause*)");

  static SATLiteralStack lits;
  lits.reset();

  unsigned clen = cl->length();
  for(unsigned i=0; i<clen; i++) {
    lits.push(ground((*cl)[i]));
  }
  SATClause* res = SATClause::fromStack(lits);
  return res;
}


class Grounder::CollapsingApplicator
{
public:
  TermList apply(unsigned var)
  {
    return TermList(0, false);
  }
};

/**
 * Return literal that has all variables replaced by variable
 * number zero.
 */
Literal* Grounder::collapseVars(Literal* lit)
{
  CALL("Grounder::collapseVars");

  CollapsingApplicator apl;
  return SubstHelper::apply(lit, apl);
}

/**
 * Return SATLiteral corresponding to @c lit.
 */
SATLiteral Grounder::ground(Literal* lit)
{
  CALL("Grounder::ground(Literal*)");

  bool positive = lit->isPositive();
  Literal* collapsed = collapseVars(lit);
  Literal* normal = positive ? collapsed : Literal::oppositeLiteral(collapsed);

  unsigned* pvar;
  if(_asgn.getValuePtr(normal, pvar)) {
    *pvar = _nextSatVar++;
  }
  return SATLiteral(*pvar, positive);
}

}
