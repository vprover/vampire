/**
 * @file Grounder.cpp
 * Implements class Grounder.
 */

#include "Lib/SharedSet.hpp"

#include "Kernel/BDD.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Renaming.hpp"
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
 * Return SATClauseIterator with SAT clauses that are results
 * of grounding of @c cl.
 */
SATClauseIterator Grounder::ground(Clause* cl)
{
  CALL("Grounder::ground(Clause*)");

  if(cl->splits() && cl->splits()->size()!=0) {
    NOT_IMPLEMENTED;
  }

  if(cl->prop() && !BDD::instance()->isFalse(cl->prop())) {
    NOT_IMPLEMENTED;
  }

  SATClause* gndNonProp = groundNonProp(cl);

  SATInference* inf = new FOConversionInference(InferenceStore::UnitSpec(cl));
  gndNonProp->setInference(inf);
  return pvi( getSingletonIterator(gndNonProp) );
}

/**
 * Return SATClause that is a result of grounding of the
 * non-propositional part of @c cl.
 *
 * The order of literals in @c cl is preserved.
 */
SATClause* Grounder::groundNonProp(Clause* cl)
{
  CALL("Grounder::groundNonProp/1");

  static SATLiteralStack gndLits;
  gndLits.reset();

  groundNonProp(cl, gndLits);

  SATClause* res = SATClause::fromStack(gndLits);
  return res;
}

/**
 * Return SATClause that is a result of grounding of the
 * non-propositional part of @c cl.
 *
 * The order of literals in @c cl is preserved.
 */
void Grounder::groundNonProp(Clause* cl, SATLiteralStack& acc)
{
  CALL("Grounder::groundNonProp/2");

  static DArray<Literal*> lits;

  unsigned clen = cl->length();
  lits.initFromArray(clen, *cl);

  normalize(clen, lits.array());

  for(unsigned i=0; i<clen; i++) {
    acc.push(groundNormalized(lits[i]));
  }
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


////////////////////////////////
// GlobalSubsumptionGrounder
//

void GlobalSubsumptionGrounder::normalize(unsigned cnt, Literal** lits)
{
  CALL("GlobalSubsumptionGrounder::normalize");

  //TODO: maybe try somehow normalize the order of literals

  static Renaming normalizer;
  normalizer.reset();

  for(unsigned i=0; i<cnt; i++) {
    normalizer.normalizeVariables(lits[i]);
    lits[i] = normalizer.apply(lits[i]);
  }
}


/////////////////
// IGGrounder
//

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
