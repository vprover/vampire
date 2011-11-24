/**
 * @file Grounder.cpp
 * Implements class Grounder.
 */

#include "Lib/Environment.hpp"
#include "Lib/SharedSet.hpp"

#include "Kernel/BDD.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/Renaming.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
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

  if(!cl->noSplits()) {
    NOT_IMPLEMENTED;
  }

  if(!cl->noProp()) {
    NOT_IMPLEMENTED;
  }

  SATClause* gndNonProp = groundNonProp(cl);
//  cout<<gndNonProp->toString()<<endl;

  SATInference* inf = new FOConversionInference(UnitSpec(cl));
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
  Literal* posLit = isPos ? lit : Literal::complementaryLiteral(lit);

  unsigned* pvar;
  if(_asgn.getValuePtr(posLit, pvar)) {
    *pvar = _nextSatVar++;
  }
  return SATLiteral(*pvar, isPos);
}

LiteralIterator Grounder::groundedLits()
{
  CALL("Grounder::groundedLits");

  return _asgn.domain();
}

void Grounder::recordInference(Clause* origClause, SATClause* refutation, Clause* resultClause)
{
  CALL("Grounder::recordInference");
  ASS(refutation);

  static Stack<UnitSpec> prems;
  static Stack<SATClause*> toDo;
  static DHSet<SATClause*> seen;
  prems.reset();
  toDo.reset();
  seen.reset();

  if(origClause) {
    prems.push(UnitSpec(origClause));
  }

  toDo.push(refutation);
  while(toDo.isNonEmpty()) {
    SATClause* cur = toDo.pop();
    if(!seen.insert(cur)) {
      continue;
    }
    SATInference* sinf = cur->inference();
    ASS(sinf);
    switch(sinf->getType()) {
    case SATInference::FO_CONVERSION:
      prems.push(static_cast<FOConversionInference*>(sinf)->getOrigin());
//      cout<<prems.top().unit()->number()<<" ";
      break;
    case SATInference::ASSUMPTION:
      break;
    case SATInference::PROP_INF:
    {
      PropInference* pinf = static_cast<PropInference*>(sinf);
      toDo.loadFromIterator(SATClauseList::Iterator(pinf->getPremises()));
      break;
    }
    default:
      ASSERTION_VIOLATION;
    }
  }

  makeUnique(prems);
  unsigned premCnt = prems.size();

  InferenceStore::FullInference* inf = new(premCnt) InferenceStore::FullInference(premCnt);
  inf->rule = Inference::GLOBAL_SUBSUMPTION;

  for(unsigned i=0; i<premCnt; i++) {
    inf->premises[i] = prems[i];
  }

  InferenceStore::instance()->recordInference(UnitSpec(resultClause), inf);
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

IGGrounder::IGGrounder()
{
  _tgtTerm = TermList(0, false);
  //TODO: make instantiation happen with the most prolific symbol of each sort
/*  unsigned funs = env.signature->functions();
  for(unsigned i=0; i<funs; i++) {
    if(env.signature->functionArity(i)==0) {
      _tgtTerm = TermList(Term::createConstant(i));
      break;
    }
  }*/
}

class IGGrounder::CollapsingApplicator
{
  TermList _tgtTerm;
public:
  CollapsingApplicator(TermList tgtTerm) : _tgtTerm(tgtTerm) {}
  TermList apply(unsigned var)
  {
//    return TermList(0, false);
    return _tgtTerm;
  }
};

/**
 * Return literal that has all variables replaced by variable
 * number zero.
 */
Literal* IGGrounder::collapseVars(Literal* lit)
{
  CALL("IGGrounder::collapseVars");

  CollapsingApplicator apl(_tgtTerm);
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
