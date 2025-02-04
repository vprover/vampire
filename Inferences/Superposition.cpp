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
 * @file Superposition.cpp
 * Implements class Superposition.
 */

#include "Debug/RuntimeStatistics.hpp"

#include "Forwards.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/PairUtils.hpp"
#include "Lib/Recycled.hpp"
#include "Lib/VirtualIterator.hpp"
#include "Lib/Set.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/ColorHelper.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/LiteralSelector.hpp"
#include "Kernel/RobSubstitution.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/IndexManager.hpp"
#include "Indexing/TermSharing.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/AnswerLiteralManager.hpp"
#include "Shell/ConditionalRedundancyHandler.hpp"
#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"
#include "Debug/TimeProfiling.hpp"

#include "Superposition.hpp"

#if VDEBUG
#include <iostream>
using namespace std;
#endif

using namespace Inferences;
using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;
using std::pair;

void Superposition::attach(SaturationAlgorithm* salg)
{
  GeneratingInferenceEngine::attach(salg);
  _subtermIndex=static_cast<SuperpositionSubtermIndex*> (
	  _salg->getIndexManager()->request(SUPERPOSITION_SUBTERM_SUBST_TREE) );
  _lhsIndex=static_cast<SuperpositionLHSIndex*> (
	  _salg->getIndexManager()->request(SUPERPOSITION_LHS_SUBST_TREE) );
}

void Superposition::detach()
{
  _subtermIndex=0;
  _lhsIndex=0;
  _salg->getIndexManager()->release(SUPERPOSITION_SUBTERM_SUBST_TREE);
  _salg->getIndexManager()->release(SUPERPOSITION_LHS_SUBST_TREE);
  GeneratingInferenceEngine::detach();
}

struct Superposition::ForwardResultFn
{
  ForwardResultFn(Clause* cl, Superposition& parent) : _cl(cl), _parent(parent) {}
  Clause* operator()(pair<pair<Literal*, TypedTermList>, QueryRes<AbstractingUnifier*, TermLiteralClause>> arg)
  {
    auto& qr = arg.second;
    return _parent.performSuperposition(_cl, arg.first.first, arg.first.second,
	    qr.data->clause, qr.data->literal, qr.data->term, qr.unifier, true);
  }
private:
  Clause* _cl;
  Superposition& _parent;
};


struct Superposition::BackwardResultFn
{
  BackwardResultFn(Clause* cl, Superposition& parent) : _cl(cl), _parent(parent) {}
  Clause* operator()(pair<pair<Literal*, TermList>, QueryRes<AbstractingUnifier*, TermLiteralClause>> arg)
  {
    if(_cl==arg.second.data->clause) {
      return 0;
    }

    auto& qr = arg.second;
    return _parent.performSuperposition(qr.data->clause, qr.data->literal, qr.data->term,
	    _cl, arg.first.first, arg.first.second, qr.unifier, false);
  }
private:
  Clause* _cl;
  Superposition& _parent;
};


ClauseIterator Superposition::generateClauses(Clause* premise)
{
  auto itf1 = premise->getSelectedLiteralIterator();

  // Get an iterator of pairs of selected literals and rewritable subterms of those literals
  // A subterm is rewritable (see EqHelper) if it is a non-variable subterm of either
  // a maximal side of an equality or of a non-equational literal
  auto itf2 = getMapAndFlattenIterator(itf1,
      [this](Literal* lit)
      // returns an iterator over the rewritable subterms
      { return pushPairIntoRightIterator(lit, env.options->combinatorySup() ? EqHelper::getFoSubtermIterator(lit, _salg->getOrdering())
                                                                            : EqHelper::getSubtermIterator(lit,  _salg->getOrdering())); });

  // Get clauses with a literal whose complement unifies with the rewritable subterm,
  // returns a pair with the original pair and the unification result (includes substitution)
  auto itf3 = getMapAndFlattenIterator(itf2,
      [this](pair<Literal*, TypedTermList> arg)
      { return pushPairIntoRightIterator(arg, _lhsIndex->getUwa(arg.second, env.options->unificationWithAbstraction(), env.options->unificationWithAbstractionFixedPointIteration())); });

  //Perform forward superposition
  auto itf4 = getMappingIterator(itf3,ForwardResultFn(premise, *this));

  auto itb1 = premise->getSelectedLiteralIterator();
  auto itb2 = getMapAndFlattenIterator(itb1,EqHelper::SuperpositionLHSIteratorFn(_salg->getOrdering(), _salg->getOptions()));
  auto itb3 = getMapAndFlattenIterator(itb2,
      [this] (pair<Literal*, TermList> arg)
      { return pushPairIntoRightIterator(
              arg,
              _subtermIndex->getUwa(TypedTermList(arg.second, SortHelper::getEqualityArgumentSort(arg.first)), env.options->unificationWithAbstraction(), env.options->unificationWithAbstractionFixedPointIteration())); });

  //Perform backward superposition
  auto itb4 = getMappingIterator(itb3,BackwardResultFn(premise, *this));

  // Add the results of forward and backward together
  auto it5 = concatIters(itf4,itb4);

  // Remove null elements - these can come from performSuperposition
  auto it6 = getFilteredIterator(it5,NonzeroFn());

  // The outer iterator ensures we update the time counter for superposition
  auto it7 = TIME_TRACE_ITER("superposition", it6);

  return pvi( it7 );
}

/**
 * Return true iff superposition of @c eqClause into @c rwClause can be performed
 * with respect to colors of the clauses. If the inference is not possible, based
 * on the value of relevant options, report the failure, and/or attempt unblocking
 * the clauses.
 *
 * This function also updates the statistics.
 */
bool Superposition::checkClauseColorCompatibility(Clause* eqClause, Clause* rwClause)
{
  if(ColorHelper::compatible(rwClause->color(), eqClause->color())) {
    return true;
  }
  if(getOptions().showBlocked()) {
    std::cout<<"Blocked superposition of "<<eqClause->toString()<<" into "<<rwClause->toString()<<std::endl;
  }
  env.statistics->inferencesSkippedDueToColors++;
  return false;
}

/**
 * Return false iff superposition from variable @c eqLHS should not be
 * performed.
 *
 * This function checks that we don't perform superpositions from
 * variables that occur in the remaining part of the clause either in
 * a literal which is not an equality, or in a as an argument of a function.
 * Such situation would mean that there is no ground substitution in which
 * @c eqLHS would be the larger argument of the largest literal.
 */
bool Superposition::checkSuperpositionFromVariable(Clause* eqClause, Literal* eqLit, TermList eqLHS)
{
  ASS(eqLHS.isVar());
  //if we should do rewriting, LHS cannot appear inside RHS
  //ASS_REP(!EqHelper::getOtherEqualitySide(eqLit, eqLHS).containsSubterm(eqLHS), eqLit->toString());

  unsigned clen = eqClause->length();
  for(unsigned i=0; i<clen; i++) {
    Literal* lit = (*eqClause)[i];
    if(lit==eqLit) {
      continue;
    }
    if(lit->isEquality()) {
      for(unsigned aIdx=0; aIdx<2; aIdx++) {
	TermList arg = *lit->nthArgument(aIdx);
	if(arg.isTerm() && arg.containsSubterm(eqLHS)) {
	  return false;
	}
      }
    }
    else if(lit->containsSubterm(eqLHS)) {
      return false;
    }
  }

  return true;
}

/**
 * If the weight of the superposition result will be greater than
 * @c weightLimit, increase the counter of discarded non-redundant
 * clauses and return false. Otherwise return true.
 *
 * The fact that true is returned doesn't mean that the weight of
 * the resulting clause will not be over the weight limit, just that
 * it cannot be cheaply determined at this time.
 */
bool Superposition::earlyWeightLimitCheck(Clause* eqClause, Literal* eqLit,
      Clause* rwClause, Literal* rwLit, TermList rwTerm, TermList eqLHS, TermList eqRHS,
      ResultSubstitutionSP subst, bool eqIsResult, PassiveClauseContainer* passiveClauseContainer, unsigned numPositiveLiteralsLowerBound, const Inference& inf)
{
  unsigned nonInvolvedLiteralWLB=0;//weight lower bound for literals that aren't going to be rewritten

  unsigned rwLength = rwClause->length();
  for(unsigned i=0;i<rwLength;i++) {
    Literal* curr=(*rwClause)[i];
    if(curr!=rwLit) {
      nonInvolvedLiteralWLB+=curr->weight();
    }
  }
  unsigned eqLength = eqClause->length();
  for(unsigned i=0;i<eqLength;i++) {
    Literal* curr=(*eqClause)[i];
    if(curr!=eqLit) {
      nonInvolvedLiteralWLB+=curr->weight();
    }
  }

  //we assume that there will be at least one rewrite in the rwLit
  if(passiveClauseContainer->exceedsWeightLimit(nonInvolvedLiteralWLB + eqRHS.weight(), numPositiveLiteralsLowerBound, inf)) {
    env.statistics->discardedNonRedundantClauses++;
    RSTAT_CTR_INC("superpositions weight skipped early");
    return false;
  }

  unsigned lhsSWeight = subst->getApplicationWeight(eqLHS, eqIsResult);
  unsigned rhsSWeight = subst->getApplicationWeight(eqRHS, eqIsResult);
  int rwrBalance = rhsSWeight-lhsSWeight;

  if(rwrBalance>=0) {
    //there must be at least one rewriting, possibly more
    unsigned approxWeight = rwLit->weight()+rwrBalance;
    if(passiveClauseContainer->exceedsWeightLimit(nonInvolvedLiteralWLB + approxWeight, numPositiveLiteralsLowerBound, inf)) {
      env.statistics->discardedNonRedundantClauses++;
      RSTAT_CTR_INC("superpositions weight skipped after rewriter weight retrieval");
      return false;
    }
  }
  //if rewrite balance is 0, it doesn't matter how many times we rewrite
  size_t rwrCnt = (rwrBalance==0) ? 0 : rwLit->countSubtermOccurrences(rwTerm);
  if(rwrCnt>1) {
    ASS_GE(rwrCnt, 1);
    unsigned approxWeight = rwLit->weight()+(rwrBalance*rwrCnt);
    if(passiveClauseContainer->exceedsWeightLimit(nonInvolvedLiteralWLB + approxWeight, numPositiveLiteralsLowerBound, inf)) {
      env.statistics->discardedNonRedundantClauses++;
      RSTAT_CTR_INC("superpositions weight skipped after rewriter weight retrieval with occurrence counting");
      return false;
    }
  }

  unsigned rwLitSWeight = subst->getApplicationWeight(rwLit, !eqIsResult);

  unsigned finalLitWeight = rwLitSWeight+(rwrBalance*rwrCnt);
  if(passiveClauseContainer->exceedsWeightLimit(nonInvolvedLiteralWLB + finalLitWeight, numPositiveLiteralsLowerBound, inf)) {
    env.statistics->discardedNonRedundantClauses++;
    RSTAT_CTR_INC("superpositions weight skipped after rewrited literal weight retrieval");
    return false;
  }

  return true;
}

/**
 * If superposition should be performed, return result of the superposition,
 * otherwise return 0.
 */
Clause* Superposition::performSuperposition(
    Clause* rwClause, Literal* rwLit, TermList rwTerm,
    Clause* eqClause, Literal* eqLit, TermList eqLHS,
    AbstractingUnifier* unifier, bool eqIsResult)
{
  TIME_TRACE("perform superposition");
  // we want the rwClause and eqClause to be active
  ASS(rwClause->store()==Clause::ACTIVE);
  ASS(eqClause->store()==Clause::ACTIVE);

  // the first checks the reference and the second checks the stack
  auto subst = ResultSubstitution::fromSubstitution(&unifier->subs(), RetrievalAlgorithms::DefaultVarBanks::query, RetrievalAlgorithms::DefaultVarBanks::internal);
  TermList eqLHSsort = SortHelper::getEqualityArgumentSort(eqLit);

  if(eqLHS.isVar()) {
    if(!checkSuperpositionFromVariable(eqClause, eqLit, eqLHS)) {
      return 0;
    }
  }

  if(!checkClauseColorCompatibility(eqClause, rwClause)) {
    return 0;
  }

  unsigned rwLength = rwClause->length();
  unsigned eqLength = eqClause->length();

  TermList tgtTerm = EqHelper::getOtherEqualitySide(eqLit, eqLHS);

  // LRS-specific optimization:
  // check whether we can conclude that the resulting clause will be discarded by LRS since it does not fulfil the age/weight limits (in which case we can discard the clause)
  // we already know the age here so we can immediately conclude whether the clause fulfils the age limit
  // since we have not built the clause yet we compute lower bounds on the weight of the clause after each step and recheck whether the weight-limit can still be fulfilled.

  unsigned numPositiveLiteralsLowerBound = Int::max(eqClause->numPositiveLiterals()-1, rwClause->numPositiveLiterals()); // lower bound on number of positive literals, don't know at this point whether duplicate positive literals will occur
  //TODO update inference rule name AYB
  Inference inf(GeneratingInference2(unifier->usesUwa() ? InferenceRule::CONSTRAINED_SUPERPOSITION : InferenceRule::SUPERPOSITION, rwClause, eqClause));
  Inference::Destroyer inf_destroyer(inf);

  auto passiveClauseContainer = _salg->getPassiveClauseContainer();
  bool andThatsIt = false;
  bool hasAgeLimitStrike = passiveClauseContainer && passiveClauseContainer->mayBeAbleToDiscriminateClausesUnderConstructionOnLimits()
                        && passiveClauseContainer->exceedsAgeLimit(numPositiveLiteralsLowerBound, inf, andThatsIt);

  if(hasAgeLimitStrike && andThatsIt) { // we are dealing with purely age-limited container (no need for weight-related investigations)
    env.statistics->discardedNonRedundantClauses++;
    RSTAT_CTR_INC("superpositions skipped for (pure) age limit before building clause");
    return 0;
  }

  if(hasAgeLimitStrike) {
    if(!earlyWeightLimitCheck(eqClause, eqLit, rwClause, rwLit, rwTerm, eqLHS, tgtTerm, subst, eqIsResult, passiveClauseContainer, numPositiveLiteralsLowerBound, inf)) {
      return 0;
    }
  }

  const auto& condRedHandler = _salg->condRedHandler();
  // if (!unifier->usesUwa()) {
  //   if (!condRedHandler.checkSuperposition(eqClause, eqLit, eqLHS, rwClause, rwLit, rwTerm, eqIsResult, subst.ptr())) {
  //     return 0;
  //   }
  // }

  const Ordering& ordering = _salg->getOrdering();

  TermList tgtTermS = subst->apply(tgtTerm, eqIsResult);

  Literal* rwLitS = subst->apply(rwLit, !eqIsResult);
  TermList rwTermS = subst->apply(rwTerm, !eqIsResult);

  //cout << "Check ordering on " << tgtTermS.toString() << " and " << rwTermS.toString() << endl;

  //check that we're not rewriting smaller subterm with larger
  auto comp = ordering.compare(tgtTermS,rwTermS);
  if(Ordering::isGreaterOrEqual(comp)) {
    return 0;
  }
  OrderingConstraints ordCons;
  if (comp == Ordering::INCOMPARABLE) {
    ordCons.push({ rwTermS, tgtTermS, Ordering::GREATER });
  }

  if(rwLitS->isEquality()) {
    //check that we're not rewriting only the smaller side of an equality
    TermList arg0=*rwLitS->nthArgument(0);
    TermList arg1=*rwLitS->nthArgument(1);

    if(!arg0.containsSubterm(rwTermS)) {
      auto comp = ordering.getEqualityArgumentOrder(rwLitS);
      if(Ordering::isGreaterOrEqual(comp)) {
        return 0;
      }
      if (comp == Ordering::INCOMPARABLE) {
        ordCons.push({ rwLitS->termArg(1), rwLitS->termArg(0), Ordering::GREATER });
      }
    } else if(!arg1.containsSubterm(rwTermS)) {
      auto comp = ordering.getEqualityArgumentOrder(rwLitS);
      if(Ordering::isGreaterOrEqual(Ordering::reverse(comp))) {
        return 0;
      }
      if (comp == Ordering::INCOMPARABLE) {
        ordCons.push({ rwLitS->termArg(0), rwLitS->termArg(1), Ordering::GREATER });
      }
    }
  }

  // if (getOptions().conditionalRedundancySubsumption()) {

    // struct Applicator : SubstApplicator {
    //   TermList operator()(unsigned v) const override {
    //     // return _cache.getOrInit(v, [&](){ return _subst->apply(TermList::var(v), _result); });
    //     return _subst->apply(TermList::var(v), _result);
    //   }
    //   void reset(ResultSubstitution* subst, bool result) {
    //     _subst = subst;
    //     _result = result;
    //     // _cache.reset();
    //   }
    //   ResultSubstitution* _subst;
    //   bool _result;
    //   // mutable Map<unsigned,TermList> _cache;
    // };

    // static Applicator rwAppl;
    // static Applicator eqAppl;
    // rwAppl.reset(subst.ptr(), !eqIsResult);
    // eqAppl.reset(subst.ptr(), eqIsResult);

    // Stack<std::pair<OrderingComparator&, const SubstApplicator*>> rights;
    // auto rwTod = static_cast<OrderingComparator*>(rwClause->getTod());
    // if (rwTod) {
    //   rights.push({ *rwTod, &rwAppl });
    // }
    // auto eqTod = static_cast<OrderingComparator*>(eqClause->getTod());
    // if (eqTod) {
    //   rights.push({ *eqTod, &eqAppl });
    // }
    // struct IdApplicator : SubstApplicator {
    //   TermList operator()(unsigned v) const override { return TermList::var(v); }
    // } idAppl;

    // Stack<std::pair<OrderingComparator&, const SubstApplicator*>> lefts;
    // for (const auto& con : ordCons) {
    //   ASS_EQ(con.rel, Ordering::GREATER);
    //   lefts.push({ *OrderingComparator::createForSingleComparison(ordering,con.lhs,con.rhs,/*ground=*/true), &idAppl });
    // }
    // ConditionalRedundancySubsumption2 subs(ordering, *infTod, rights);
    // ConditionalRedundancySubsumption3<false> subs(ordering, lefts, rights);
    // ConditionalRedundancySubsumption3<true> subsCP(ordering, rights, lefts);
    // auto res = subsCP.check();
    // if (res) {
    //   env.statistics->skippedSuperposition++;
    //   return 0;
    // }
  // }

  if (!unifier->usesUwa()) {
    if (!condRedHandler.insertSuperposition(
      eqClause, rwClause, rwTermS, tgtTermS, eqLHS, rwLitS, eqLit, comp, eqIsResult, subst.ptr()))
    {
      return 0;
    }
  }

  Literal* tgtLitS = EqHelper::replace(rwLitS,rwTermS,tgtTermS);

  static bool doSimS = getOptions().simulatenousSuperposition();

  //check we don't create an equational tautology (this happens during self-superposition)
  if(EqHelper::isEqTautology(tgtLitS)) {
    return 0;
  }

  TermList eqLHSS = subst->apply(eqLHS, eqIsResult);

#if VDEBUG
  if(!unifier->usesUwa()){
    ASS_EQ(rwTermS,eqLHSS);
  }
#endif

  Recycled<Stack<Literal*>> res;
  res->reserve(rwLength + eqLength - 1 + unifier->maxNumberOfConstraints());

  bool synthesis = (env.options->questionAnswering() == Options::QuestionAnsweringMode::SYNTHESIS);
  Literal* rwAnsLit = synthesis ? rwClause->getAnswerLiteral() : nullptr;
  Literal* eqAnsLit = synthesis ? eqClause->getAnswerLiteral() : nullptr;
  bool bothHaveAnsLit = (rwAnsLit != nullptr) && (eqAnsLit != nullptr);

  static bool afterCheck = getOptions().literalMaximalityAftercheck() && _salg->getLiteralSelector().isBGComplete();

  res->push(tgtLitS);
  unsigned weight=tgtLitS->weight();
  for(unsigned i=0;i<rwLength;i++) {
    Literal* curr=(*rwClause)[i];
    if(curr!=rwLit && (!bothHaveAnsLit || curr!=rwAnsLit)) {
      Literal* currAfter = subst->apply(curr, !eqIsResult);

      if (doSimS) {
        currAfter = EqHelper::replace(currAfter,rwTermS,tgtTermS);
      }

      if(EqHelper::isEqTautology(currAfter)) {
        return nullptr;
      }

      if(hasAgeLimitStrike) {
        weight+=currAfter->weight();
        if(passiveClauseContainer->exceedsWeightLimit(weight, numPositiveLiteralsLowerBound, inf)) {
          RSTAT_CTR_INC("superpositions skipped for weight limit while constructing other literals");
          env.statistics->discardedNonRedundantClauses++;
          return nullptr;
        }
      }

      if (afterCheck) {
        TIME_TRACE(TimeTrace::LITERAL_ORDER_AFTERCHECK)
        if (i < rwClause->numSelected() && ordering.compare(currAfter,rwLitS) == Ordering::GREATER) {
          env.statistics->inferencesBlockedForOrderingAftercheck++;
          return nullptr;
        }
      }

      res->push(currAfter);
    }
  }

  {
    Literal* eqLitS = 0;
    if (afterCheck && eqClause->numSelected() > 1) {
      TIME_TRACE(TimeTrace::LITERAL_ORDER_AFTERCHECK);
      eqLitS = Literal::createEquality(true,eqLHSS,tgtTermS,eqLHSsort);
    }

    for(unsigned i=0;i<eqLength;i++) {
      Literal* curr=(*eqClause)[i];
      if(curr!=eqLit) {
        Literal* currAfter = subst->apply(curr, eqIsResult);

        if(EqHelper::isEqTautology(currAfter)) {
          return nullptr;
        }
        if(hasAgeLimitStrike) {
          weight+=currAfter->weight();
          if(passiveClauseContainer->exceedsWeightLimit(weight, numPositiveLiteralsLowerBound, inf)) {
            RSTAT_CTR_INC("superpositions skipped for weight limit while constructing other literals");
            env.statistics->discardedNonRedundantClauses++;
            return nullptr;
          }
        }

        if (eqLitS && i < eqClause->numSelected()) {
          TIME_TRACE(TimeTrace::LITERAL_ORDER_AFTERCHECK);

          Ordering::Result o = ordering.compare(currAfter,eqLitS);

          if (o == Ordering::GREATER || o == Ordering::EQUAL) {
            env.statistics->inferencesBlockedForOrderingAftercheck++;
            return nullptr;
          }
        }

        res->push(currAfter);
      }
    }
  }

  res->loadFromIterator(unifier->computeConstraintLiterals()->iter());

  if (bothHaveAnsLit) {
    Literal* newLitC = subst->apply(rwAnsLit, !eqIsResult);
    Literal* newLitD = subst->apply(eqAnsLit, eqIsResult);
    Literal* condLit = subst->apply(eqLit, eqIsResult);
    res->push(SynthesisALManager::getInstance()->makeITEAnswerLiteral(condLit, newLitC, newLitD));
  }

  if(hasAgeLimitStrike && passiveClauseContainer->exceedsWeightLimit(weight, numPositiveLiteralsLowerBound, inf)) {
    RSTAT_CTR_INC("superpositions skipped for weight limit after the clause was built");
    env.statistics->discardedNonRedundantClauses++;
    return nullptr;
  }

  if(!unifier->usesUwa()){
    if(rwClause==eqClause) {
      env.statistics->selfSuperposition++;
    } else if(eqIsResult) {
      env.statistics->forwardSuperposition++;
    } else {
      env.statistics->backwardSuperposition++;
    }
  } else {
    if(rwClause==eqClause) {
      env.statistics->cSelfSuperposition++;
    } else if(eqIsResult) {
      env.statistics->cForwardSuperposition++;
    } else {
      env.statistics->cBackwardSuperposition++;
    }
  }

  inf_destroyer.disable(); // ownership passed to the the clause below
  auto clause = Clause::fromStack(*res, inf);

  if(env.options->proofExtra() == Options::ProofExtra::FULL)
    env.proofExtra.insert(clause, new SuperpositionExtra(
      rwLit,
      eqLit,
      eqLHS,
      rwTerm
    ));

  return clause;
}
