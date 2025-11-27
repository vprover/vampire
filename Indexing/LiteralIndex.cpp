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
 * @file LiteralIndex.cpp
 * Implements class LiteralIndex.
 */

#include "Inferences/InductionHelper.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/LiteralComparators.hpp"
#include "Kernel/LiteralByMatchability.hpp"
#include "Kernel/Matcher.hpp"
#include "Kernel/MLVariant.hpp"
#include "Kernel/Ordering.hpp"

#include "LiteralIndexingStructure.hpp"
#include "LiteralSubstitutionTree.hpp"

#include "LiteralIndex.hpp"

namespace Indexing
{

using namespace Kernel;

void BinaryResolutionIndex::handleClause(Clause* c, bool adding)
{
  TIME_TRACE("binary resolution index maintenance");

  int selCnt=c->numSelected();
  for(int i=0; i<selCnt; i++) {
    Literal* lit = (*c)[i];
    if (!lit->isEquality()) {
      handle(LiteralClause{lit, c}, adding);
    }
  }
}

void BackwardSubsumptionIndex::handleClause(Clause* c, bool adding)
{
  TIME_TRACE("backward subsumption index maintenance");

  unsigned clen=c->length();
  for(unsigned i=0; i<clen; i++) {
    handle(LiteralClause{(*c)[i], c}, adding);
  }
}


void FwSubsSimplifyingLiteralIndex::handleClause(Clause* c, bool adding)
{
  if (c->length() < 2) {
    return;
  }

  TIME_TRACE("forward subsumption index maintenance");

  Literal* best = LiteralByMatchability::find_least_matchable_in(c).lit();
  handle(LiteralClause{best, c}, adding);
}

void FSDLiteralIndex::handleClause(Clause* c, bool adding)
{
  if (c->length() < 2) {
    return;
  }

  TIME_TRACE("forward subsumption demodulation index maintenance");

  bool hasPosEquality = false;
  for (unsigned i = 0; i < c->length(); ++i) {
    Literal *lit = (*c)[i];
    if (lit->isEquality() && lit->isPositive()) {
      hasPosEquality = true;
      break;
    }
  }
  if (!hasPosEquality) {
    // We only need clauses with at least one positive equality for subsumption demodulation
    return;
  }

  auto res = LiteralByMatchability::find_two_least_matchable_in(c);
  Literal* best = res.first.lit();
  Literal* secondBest = res.second.lit();
  if (!best->isEquality() || !best->isPositive()) {
    handle(LiteralClause{best, c}, adding);
  } else if (!secondBest->isEquality() || !secondBest->isPositive()) {
    handle(LiteralClause{secondBest, c}, adding);
  } else {
    // both are positive equalities, so we need to add both
    handle(LiteralClause{best, c}, adding);
    handle(LiteralClause{secondBest, c}, adding);
  }
}

void UnitClauseLiteralIndex::handleClause(Clause* c, bool adding)
{
  if(c->length()==1) {
    TIME_TRACE("unit clause index maintenance");
    
    handle(LiteralClause{(*c)[0], c}, adding);
  }
}

void UnitClauseWithALLiteralIndex::handleClause(Clause* c, bool adding)
{
  if(c->length()==1 || (c->hasAnswerLiteral() && c->length() == 2)) {
    TIME_TRACE("unit clause with answer literals index maintenance");

    Literal* al = c->getAnswerLiteral();
    handle(LiteralClause{(*c)[(al == (*c)[0]) ? 1 : 0], c}, adding);
  }
}

void NonUnitClauseLiteralIndex::handleClause(Clause* c, bool adding)
{
  unsigned clen=c->length();
  if(clen<2) {
    return;
  }
  TIME_TRACE("non unit clause index maintenance");
  unsigned activeLen = _selectedOnly ? c->numSelected() : clen;
  for(unsigned i=0; i<activeLen; i++) {
    handle(LiteralClause{(*c)[i], c}, adding);
  }
}

void NonUnitClauseWithALLiteralIndex::handleClause(Clause* c, bool adding)
{
  unsigned clen=c->length();
  if(clen<2 || (c->hasAnswerLiteral() && clen<3)) {
    return;
  }
  TIME_TRACE("non unit clause with answer literals index maintenance");
  unsigned activeLen = _selectedOnly ? c->numSelected() : clen;
  for(unsigned i=0; i<activeLen; i++) {
    handle(LiteralClause{(*c)[i], c}, adding);
  }
}

RewriteRuleIndex::RewriteRuleIndex(LiteralIndexingStructure<LiteralClause>* is, Ordering& ordering)
: LiteralIndex(is), _ordering(ordering)
{
  _partialIndex = new LiteralSubstitutionTree<LiteralClause>();
}

RewriteRuleIndex::~RewriteRuleIndex()
{
  delete _partialIndex;
}

/**
 * For a two-literal clause return its literal that is
 * in some ordering greater, or 0 if the two literals
 * are complamentary variants of each other
 *
 * If A and B are not variants of each other, it must hold:
 * - if A>B, it also holds ~A>~B
 * - if A',B' are variants of A,B, it holds A'>B'
 */
Literal* RewriteRuleIndex::getGreater(Clause* c)
{
  ASS_EQ(c->length(), 2);

  Comparison comp = LiteralComparators::NormalizedLinearComparatorByWeight().compare((*c)[0], (*c)[1]);
  Literal* greater=
    ( comp==GREATER ) ? (*c)[0] :
    ( comp==LESS ) ? (*c)[1] : 0;

  if( !greater && (*c)[0]->polarity()==(*c)[1]->polarity() ) {
    if((*c)[0]>(*c)[1]) {
      greater=(*c)[0];
    } else {
      greater=(*c)[1];
      //the two literals are variants, but should not be equal (as
      //otherwise they would be deleted by the duplicate literal
      //removal rule)
      ASS_NEQ((*c)[0],(*c)[1])
    }
  }

  return greater;
}

void RewriteRuleIndex::handleClause(Clause* c, bool adding)
{
  if(c->length()!=2) {
    return;
  }

  TIME_TRACE("literal rewrite rule index maintenance");

  Literal* greater=getGreater(c);

  if(greater) {
    if(adding) {
      // true here means get complementary, false means do not get subs
      auto vit = _partialIndex->getVariants(greater,true,false);
      while(vit.hasNext()) {
        auto qr = vit.next();

        // true here means complementary
        if(!MLVariant::isVariant(c, qr.data->clause, true)) {
          continue;
        }

        //we have found a counterpart
        handleEquivalence(c, greater, qr.data->clause, qr.data->literal, true);
        return;
      }
      //there is no counterpart, so insert the clause into the partial index
      _partialIndex->insert(LiteralClause{ greater, c });
    }
    else {
      Clause* d;
      if(_counterparts.find(c, d)) {
	Literal* dgr=getGreater(d);
	ASS(MatchingUtils::isVariant(greater, dgr, true))
	handleEquivalence(c, greater, d, dgr, false);
      }
      else {
	_partialIndex->remove(LiteralClause{ greater, c });
      }
    }
  }
  else {
    //the two literals are complementary variants of each other, so we don't
    //need to wait for the complementary clause
    if((*c)[0]->containsAllVariablesOf((*c)[1]) && (*c)[1]->containsAllVariablesOf((*c)[0])) {
      if((*c)[0]->isPositive()) {
        handle(LiteralClause{(*c)[0], c}, adding);
      }
      else {
	ASS((*c)[1]->isPositive());
        handle(LiteralClause{(*c)[1], c}, adding);
      }
      if(adding) {
        _counterparts.insert(c, c);
      } else {
        _counterparts.remove(c);
      }
    }

  }
}

void RewriteRuleIndex::handleEquivalence(Clause* c, Literal* cgr, Clause* d, Literal* dgr, bool adding)
{
  Literal* csm = (cgr==(*c)[0]) ? (*c)[1] : (*c)[0];
  Literal* dsm = (dgr==(*d)[0]) ? (*d)[1] : (*d)[0];

  Ordering::Result cmpRes;
  //we want to always pass the greater literal as positive in order to get consistent results
  //when using the LCM_REVERSE literal comparison mode.
  if(cgr->isPositive()) {
    //we use Literal::complementaryLiteral(csm) instead of dsm (which is a variant with
    //opposite polarity), so that the literals share variables
    cmpRes=_ordering.compare(cgr,Literal::complementaryLiteral(csm));
  }
  else {
    cmpRes=_ordering.compare(Literal::complementaryLiteral(cgr),csm);
  }
  switch(cmpRes) {
  case Ordering::GREATER:
    if(cgr->containsAllVariablesOf(csm)) {
      if(cgr->isPositive()) {
        handle(LiteralClause{cgr, c}, adding);
      }
      else {
        handle(LiteralClause{dgr, d}, adding);
      }
    }
    break;
  case Ordering::LESS:
    if(csm->containsAllVariablesOf(cgr)) {
      if(csm->isPositive()) {
        handle(LiteralClause{csm, c}, adding);
      }
      else {
        handle(LiteralClause{dsm, d}, adding);
      }
    }
    break;
  case Ordering::INCOMPARABLE:
    if(cgr->containsAllVariablesOf(csm)) {
      if(cgr->isPositive()) {
        handle(LiteralClause{cgr, c}, adding);
      }
      else {
        handle(LiteralClause{dgr, d}, adding);
      }
    }
    if(csm->containsAllVariablesOf(cgr)) {
      if(csm->isPositive()) {
        handle(LiteralClause{csm, c}, adding);
      }
      else {
        handle(LiteralClause{dsm, d}, adding);
      }
    }
    break;
  case Ordering::EQUAL:
    //equal meant they're variants which we have checked for earlier
    ASSERTION_VIOLATION;
  }

  if(adding) {
    ALWAYS(_counterparts.insert(c, d));
    ALWAYS(_counterparts.insert(d, c));

    //we can remove the literal from the index of partial definitions
    _partialIndex->remove(LiteralClause{ dgr, d });
  }
  else {
    _counterparts.remove(c);
    _counterparts.remove(d);

    //we put the remaining counterpart into the index of partial definitions
    _partialIndex->insert(LiteralClause{ dgr, d });
  }

}


/**
 * 
 * We assume the clause has already been instantiated
 * Just add/remove each term to the indexing structure
 *
 * TODO - this should not be used with the general substitution tree
 *        index as it is memory inefficient, and expensive to create
 *
 * @author Giles
 */
void DismatchingLiteralIndex::handleClause(Clause* c, bool adding)
{
  //TODO add time counter for dismatching

  unsigned clen=c->length();
  for(unsigned i=0; i<clen; i++) {
    handle(LiteralClause{(*c)[i], c}, adding);
  }
}
void DismatchingLiteralIndex::addLiteral(Literal* l)
{
  //TODO is it safe to pass 0 here?
  handle(LiteralClause{l,0},true);
}

void UnitIntegerComparisonLiteralIndex::handleClause(Clause* c, bool adding)
{
  TIME_TRACE("unit integer comparison literal index maintenance");
  
  if (!Inferences::InductionHelper::isIntegerComparison(c)) {
    return;
  }

  Literal* lit = (*c)[0];
  ASS(lit != nullptr);

  _is->handle(LiteralClause{ lit, c }, adding);
}

}
