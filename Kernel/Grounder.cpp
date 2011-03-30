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

namespace Kernel
{

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

  static DArray<Literal*> lits;
  static SATLiteralStack gndLits;
  gndLits.reset();

  unsigned clen = cl->length();
  lits.initFromArray(clen, *cl);

  normalize(clen, lits.array());

  for(unsigned i=0; i<clen; i++) {
    gndLits.push(groundNormalized(lits[i]));
  }
  SATClause* res = SATClause::fromStack(gndLits);
  return res;
}

/**
 * Return SATLiteral corresponding to @c lit.
 */
SATLiteral Grounder::ground(Literal* lit)
{
  CALL("Grounder::ground(Literal*)");

  Literal* norm = lit;
  normalize(1, &norm);
  return groundNormalized(norm);
}

/**
 * Return SATLiteral corresponding to @c lit.
 */
SATLiteral Grounder::groundNormalized(Literal* lit)
{
  CALL("Grounder::groundNormalized");

  bool isPos = lit->isPositive();
  Literal* posLit = isPos ? lit : Literal::oppositeLiteral(lit);

  unsigned* pvar;
  if(_asgn.getValuePtr(posLit, pvar)) {
    *pvar = _nextSatVar++;
  }
  return SATLiteral(*pvar, isPos);
}

class IGGrounder::CollapsingApplicator
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
Literal* IGGrounder::collapseVars(Literal* lit)
{
  CALL("IGGrounder::collapseVars");

  CollapsingApplicator apl;
  return SubstHelper::apply(lit, apl);
}

void IGGrounder::normalize(unsigned cnt, Literal** lits)
{
  CALL("IGGrounder::normalize");

  for(unsigned i=0; i<cnt; i++) {
    lits[i] = collapseVars(lits[i]);
  }
}

}
