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

LiteralIndex::~LiteralIndex()
{
  delete _is;
}

SLQueryResultIterator LiteralIndex::getAll()
{
  return _is->getAll();
}

SLQueryResultIterator LiteralIndex::getUnifications(Literal* lit,
	  bool complementary, bool retrieveSubstitutions)
{
  return _is->getUnifications(lit, complementary, retrieveSubstitutions);
}

SLQueryResultIterator LiteralIndex::getUnificationsWithConstraints(Literal* lit,
          bool complementary, bool retrieveSubstitutions)
{
  return _is->getUnificationsWithConstraints(lit, complementary, retrieveSubstitutions);
}

SLQueryResultIterator LiteralIndex::getGeneralizations(Literal* lit,
	  bool complementary, bool retrieveSubstitutions)
{
  return _is->getGeneralizations(lit, complementary, retrieveSubstitutions);
}

SLQueryResultIterator LiteralIndex::getInstances(Literal* lit,
	  bool complementary, bool retrieveSubstitutions)
{
  return _is->getInstances(lit, complementary, retrieveSubstitutions);
}

size_t LiteralIndex::getUnificationCount(Literal* lit, bool complementary)
{
  return _is->getUnificationCount(lit, complementary);
}

void LiteralIndex::handleLiteral(Literal* lit, Clause* cl, bool add)
{
  CALL("LiteralIndex::handleLiteral");

  if(add) {
    _is->insert(lit, cl);
  } else {
    _is->remove(lit, cl);
  }
}

void GeneratingLiteralIndex::handleClause(Clause* c, bool adding)
{
  CALL("GeneratingLiteralIndex::handleClause");

  TimeCounter tc(TC_BINARY_RESOLUTION_INDEX_MAINTENANCE);

  int selCnt=c->numSelected();
  for(int i=0; i<selCnt; i++) {
    handleLiteral((*c)[i], c, adding);
  }
}

void SimplifyingLiteralIndex::handleClause(Clause* c, bool adding)
{
  CALL("SimplifyingLiteralIndex::handleClause");

  TimeCounter tc(TC_BACKWARD_SUBSUMPTION_INDEX_MAINTENANCE);

  unsigned clen=c->length();
  for(unsigned i=0; i<clen; i++) {
    handleLiteral((*c)[i], c, adding);
  }
}


void FwSubsSimplifyingLiteralIndex::handleClause(Clause* c, bool adding)
{
  CALL("FwSubsSimplifyingLiteralIndex::handleClause");

  if (c->length() < 2) {
    return;
  }

  TimeCounter tc(TC_FORWARD_SUBSUMPTION_INDEX_MAINTENANCE);

  Literal* best = LiteralByMatchability::find_least_matchable_in(c).lit();
  handleLiteral(best, c, adding);
}

void FSDLiteralIndex::handleClause(Clause* c, bool adding)
{
  CALL("FSDLiteralIndex::handleClause");

  if (c->length() < 2) {
    return;
  }

  TimeCounter tc(TC_FORWARD_SUBSUMPTION_DEMODULATION_INDEX_MAINTENANCE);

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
    handleLiteral(best, c, adding);
  } else if (!secondBest->isEquality() || !secondBest->isPositive()) {
    handleLiteral(secondBest, c, adding);
  } else {
    // both are positive equalities, so we need to add both
    handleLiteral(best, c, adding);
    handleLiteral(secondBest, c, adding);
  }
}

void UnitClauseLiteralIndex::handleClause(Clause* c, bool adding)
{
  CALL("UnitClauseLiteralIndex::handleClause");

  if(c->length()==1) {
    TimeCounter tc(TC_SIMPLIFYING_UNIT_LITERAL_INDEX_MAINTENANCE);

    handleLiteral((*c)[0], c, adding);
  }
}

void NonUnitClauseLiteralIndex::handleClause(Clause* c, bool adding)
{
  CALL("NonUnitClauseLiteralIndex::handleClause");

  unsigned clen=c->length();
  if(clen<2) {
    return;
  }
  TimeCounter tc(TC_NON_UNIT_LITERAL_INDEX_MAINTENANCE);
  unsigned activeLen = _selectedOnly ? c->numSelected() : clen;
  for(unsigned i=0; i<activeLen; i++) {
    handleLiteral((*c)[i], c, adding);
  }
}

RewriteRuleIndex::RewriteRuleIndex(LiteralIndexingStructure* is, Ordering& ordering)
: LiteralIndex(is), _ordering(ordering)
{
  _partialIndex=new LiteralSubstitutionTree();
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
  CALL("RewriteRuleIndex::getGreater");
  ASS_EQ(c->length(), 2);

  static LiteralComparators::NormalizedLinearComparatorByWeight<true> comparator;

  Comparison comp=comparator.compare((*c)[0], (*c)[1]);

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
  CALL("RewriteRuleIndex::handleClause");

  if(c->length()!=2) {
    return;
  }

  TimeCounter tc(TC_LITERAL_REWRITE_RULE_INDEX_MAINTENANCE);

  Literal* greater=getGreater(c);

  if(greater) {
    if(adding) {
      // true here means get complementary, false means do not get subs
      SLQueryResultIterator vit=_partialIndex->getVariants(greater,true,false);
      while(vit.hasNext()) {
        SLQueryResult qr=vit.next();

        // true here means complementary
        if(!MLVariant::isVariant(c ,qr.clause, true)) {
          continue;
        }

        //we have found a counterpart
        handleEquivalence(c, greater, qr.clause, qr.literal, true);
        return;
      }
      //there is no counterpart, so insert the clause into the partial index
      _partialIndex->insert(greater, c);
    }
    else {
      Clause* d;
      if(_counterparts.find(c, d)) {
	Literal* dgr=getGreater(d);
	ASS(MatchingUtils::isVariant(greater, dgr, true))
	handleEquivalence(c, greater, d, dgr, false);
      }
      else {
	_partialIndex->remove(greater, c);
      }
    }
  }
  else {
    //the two literals are complementary variants of each other, so we don't
    //need to wait for the complementary clause
    if((*c)[0]->containsAllVariablesOf((*c)[1]) && (*c)[1]->containsAllVariablesOf((*c)[0])) {
      if((*c)[0]->isPositive()) {
	handleLiteral((*c)[0], c, adding);
      }
      else {
	ASS((*c)[1]->isPositive());
	handleLiteral((*c)[1], c, adding);
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
  CALL("RewriteRuleIndex::handleEquivalence");

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
  case Ordering::GREATER_EQ:
    if(cgr->containsAllVariablesOf(csm)) {
      if(cgr->isPositive()) {
        handleLiteral(cgr, c, adding);
      }
      else {
        handleLiteral(dgr, d, adding);
      }
    }
    break;
  case Ordering::LESS:
  case Ordering::LESS_EQ:
    if(csm->containsAllVariablesOf(cgr)) {
      if(csm->isPositive()) {
        handleLiteral(csm, c, adding);
      }
      else {
        handleLiteral(dsm, d, adding);
      }
    }
    break;
  case Ordering::INCOMPARABLE:
    if(cgr->containsAllVariablesOf(csm)) {
      if(cgr->isPositive()) {
	handleLiteral(cgr, c, adding);
      }
      else {
	handleLiteral(dgr, d, adding);
      }
    }
    if(csm->containsAllVariablesOf(cgr)) {
      if(csm->isPositive()) {
	handleLiteral(csm, c, adding);
      }
      else {
	handleLiteral(dsm, d, adding);
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
    _partialIndex->remove(dgr, d);
  }
  else {
    _counterparts.remove(c);
    _counterparts.remove(d);

    //we put the remaining counterpart into the index of partial definitions
    _partialIndex->insert(dgr, d);
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
  CALL("DismatchingLiteralIndex::handleClause");

  //TODO add time counter for dismatching

  unsigned clen=c->length();
  for(unsigned i=0; i<clen; i++) {
    handleLiteral((*c)[i], c, adding);
  }
}
void DismatchingLiteralIndex::addLiteral(Literal* l)
{
  CALL("DismatchingLiteralIndex::addLiteral");
  //TODO is it safe to pass 0 here?
  handleLiteral(l,0,true);
}

void UnitIntegerComparisonLiteralIndex::handleClause(Clause* c, bool adding)
{
  CALL("UnitIntegerComparisonLiteralIndex::handleClause");

  TimeCounter tc(TC_UNIT_INTEGER_COMPARISON_INDEX_MAINTENANCE);
  
  if (!Inferences::InductionHelper::isIntegerComparison(c)) {
    return;
  }

  Literal* lit = (*c)[0];
  ASS(lit != nullptr);

  if (adding) {
    _is->insert(lit, c);
  } else {
    _is->remove(lit, c);
  }
}

}
