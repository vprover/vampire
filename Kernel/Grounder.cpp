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
 * @file Grounder.cpp
 * Implements class Grounder.
 */

#include <algorithm>

#include "Lib/Environment.hpp"
#include "Lib/SharedSet.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/Renaming.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"

#include "SAT/SATClause.hpp"
#include "SAT/SATInference.hpp"
#include "SAT/SATLiteral.hpp"
#include "SAT/SATSolver.hpp"

#include "Grounder.hpp"

using namespace Kernel;

/**
 * Return SATClauseIterator with SAT clauses that are results
 * of grounding of @c cl.
 */
SATClause* Grounder::ground(Clause* cl)
{
  CALL("Grounder::ground(Clause*)");

  if(!cl->noSplits()) {
    NOT_IMPLEMENTED;
  }

  SATClause* gndNonProp = groundNonProp(cl);
//  cout<<gndNonProp->toString()<<endl;

  SATInference* inf = new FOConversionInference(cl);
  gndNonProp->setInference(inf);

  return gndNonProp;
}

/**
 * Return SATClause that is a result of grounding of the
 * non-propositional part of @c cl.
 *
 * The order of literals in @c cl is preserved.
 *
 * @param cl the clause
 * @param acc previously accumulated literals
 * @param normLits if non-zero, array to receive normalized literals
 * (in the order of literals in the clause). Size of the array must be
 * at least equal to te size of the clause. There is one-to-one
 * correspondence between normalized literals and SAT literals.
 */
void Grounder::groundNonProp(Clause* cl, SATLiteralStack& acc, Literal** normLits)
{
  CALL("Grounder::groundNonProp/2");

  static DArray<Literal*> lits;

  unsigned clen = cl->length();

  if(normLits) {
    std::copy(cl->literals(), cl->literals()+clen, normLits);
  }
  else {
    lits.initFromArray(clen, *cl);
    normLits = lits.array();
  }

  normalize(clen, normLits);

  for(unsigned i=0; i<clen; i++) {
    SATLiteral lit = groundNormalized(normLits[i]);
    acc.push(lit);
  }
}

/**
 * Return SATClause that is a result of grounding of the
 * non-propositional part of @c cl.
 *
 * The order of literals in @c cl is preserved.
 *
 * @param cl the clause
 * @param normLits if non-zero, array to receive normalized literals
 * (in the order of literals in the clause). Size of the array must be
 * at least equal to te size of the clause. There is one-to-one
 * correspondence between normalized literals and SAT literals.
 */
SATClause* Grounder::groundNonProp(Clause* cl, Literal** normLits)
{
  CALL("Grounder::groundNonProp(Clause*,Literal**)");

  static SATLiteralStack gndLits;
  gndLits.reset();

  groundNonProp(cl, gndLits, normLits);

  SATClause* res = SATClause::fromStack(gndLits);
  return res;
}

/**
 * Return SATLiteral corresponding to @c lit.
 */
SATLiteral Grounder::groundLiteral(Literal* lit)
{
  CALL("Grounder::ground(Literal*)");

  Literal* norm = lit;
  normalize(1, &norm);
  SATLiteral slit = groundNormalized(norm);
  return slit;
}

/**
 * Return SATLiteral corresponding to @c lit.
 */
SATLiteral Grounder::groundNormalized(Literal* lit)
{
  CALL("Grounder::groundNormalized");

  bool isPos = lit->isPositive();
  Literal* posLit = Literal::positiveLiteral(lit);

  unsigned* pvar;
  if(_asgn.getValuePtr(posLit, pvar)) {    
    *pvar = _satSolver->newVar();
  }
  return SATLiteral(*pvar, isPos);
}

LiteralIterator Grounder::groundedLits()
{
  CALL("Grounder::groundedLits");

  return _asgn.domain();
}


////////////////////////////////
// GlobalSubsumptionGrounder
//

struct GlobalSubsumptionGrounder::OrderNormalizingComparator
{
  Literal** _lits;
  OrderNormalizingComparator(Literal** lits) : _lits(lits) {}

  bool operator()(unsigned a, unsigned b) {
    Literal* la = _lits[a];
    Literal* lb = _lits[b];
    if(la==lb) { return false; }
    if(la->vars()!=lb->vars()) {
      //first, we want literals with less variables to appear in the
      //beginning as there is better chance to get some sharing across clauses
      return la->vars()<lb->vars();
    }
    if(la->weight()!=lb->weight()) {
      return la->weight()<lb->weight();
    }
    if(la->header()!=lb->header()) {
      return la->header()<lb->header();
    }
    //now get just some total deterministic order
    static DisagreementSetIterator dsit;
    dsit.reset(la, lb, false);
    ALWAYS(dsit.hasNext());
    pair<TermList,TermList> da = dsit.next();
    if(da.first.isVar()!=da.second.isVar()) {
      return da.first.isVar();
    }
    if(da.first.isVar()) {
      ASS_NEQ(da.first.var(),da.second.var());
      return da.first.var()<da.second.var();
    }
    else {
      ASS_NEQ(da.first.term()->functor(),da.second.term()->functor());
      return da.first.term()->functor()<da.second.term()->functor();
    }
    return a<b; //if nothing else applies, we keep the original order
  }
};

void GlobalSubsumptionGrounder::normalize(unsigned cnt, Literal** lits)
{
  CALL("GlobalSubsumptionGrounder::normalize");

  if(!_doNormalization) { return; }

  if(cnt==0) { return; }
  if(cnt==1) {
    lits[0] = Renaming::normalize(lits[0]);
  }

  static Stack<unsigned> litOrder;
  litOrder.reset();
  litOrder.loadFromIterator(getRangeIterator(0u,cnt));

  std::sort(litOrder.begin(), litOrder.end(), OrderNormalizingComparator(lits));

  static Renaming normalizer;
  normalizer.reset();

  for(unsigned i=0; i<cnt; i++) {
    unsigned li = litOrder[i];
    normalizer.normalizeVariables(lits[li]);
    lits[li] = normalizer.apply(lits[li]);
  }
}


/////////////////
// IGGrounder
//

IGGrounder::IGGrounder(SATSolver* satSolver) : Grounder(satSolver)
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

