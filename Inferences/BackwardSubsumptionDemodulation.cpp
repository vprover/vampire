/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */


#include "Debug/RuntimeStatistics.hpp"

#include "Lib/DArray.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/Environment.hpp"
#include "Lib/List.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/ScopeGuard.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/ColorHelper.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/LiteralByMatchability.hpp"
#include "Kernel/MLMatcherSD.hpp"
#include "Kernel/Matcher.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/OperatorType.hpp"
#include "Kernel/Term.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/LiteralIndex.hpp"
#include "Indexing/LiteralMiniIndex.hpp"
#include "Indexing/IndexManager.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Statistics.hpp"
#include "Shell/TPTPPrinter.hpp"

#include "BackwardSubsumptionDemodulation.hpp"
#include "SubsumptionDemodulationHelper.hpp"



namespace Inferences
{

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;


BackwardSubsumptionDemodulation::BackwardSubsumptionDemodulation()
  : _preorderedOnly{false}
  , _allowIncompleteness{false}
{ }


void BackwardSubsumptionDemodulation::attach(SaturationAlgorithm* salg)
{
  CALL("BackwardSubsumptionDemodulation::attach");
  BackwardSimplificationEngine::attach(salg);

  _index.request(salg->getIndexManager(), SIMPLIFYING_SUBST_TREE);
}


void BackwardSubsumptionDemodulation::detach()
{
  CALL("BackwardSubsumptionDemodulation::detach");
  _index.release();
  BackwardSimplificationEngine::detach();
}


template <typename Iterator>
class STLIterator
{
  private:
    Iterator begin;
    Iterator end;

  public:
    using value_type = typename Iterator::value_type;
    DECL_ELEMENT_TYPE(value_type);

    STLIterator(Iterator begin, Iterator end)
      : begin(begin), end(end)
    { }

    bool hasNext() {
      return begin != end;
    }

    value_type next() {
      value_type x = *begin;
      ++begin;
      return x;
    }
};

template <typename Iterator>
STLIterator<Iterator> getSTLIterator(Iterator begin, Iterator end)
{
  return STLIterator<Iterator>(begin, end);
}


void BackwardSubsumptionDemodulation::perform(Clause* sideCl, BwSimplificationRecordIterator& simplifications)
{
  CALL("BackwardSubsumptionDemodulation::perform");
  ASSERT_VALID(*sideCl);

  TimeCounter tc(TC_BACKWARD_SUBSUMPTION_DEMODULATION);

  simplifications = BwSimplificationRecordIterator::getEmpty();

  if (sideCl->length() == 0) {
    // No BSD with empty side clause possible
    return;
  }

  if (sideCl->length() == 1) {
    // Handled by regular backward demodulation
    return;
  }

  bool hasPositiveEquality = false;
  for (unsigned i = 0; i < sideCl->length(); ++i) {
    Literal* lit = (*sideCl)[i];
    if (lit->isEquality() && lit->isPositive()) {
      hasPositiveEquality = true;
      break;
    }
  }
  if (!hasPositiveEquality) {
    // no SD is possible if we do not have a positive equality in the side premise
    return;
  }

  // We use clause aux value to store whether a candidate clause has been checked already
  Clause::requestAux();
  ON_SCOPE_EXIT({ Clause::releaseAux(); });

  auto best2 = LiteralByMatchability::find_two_least_matchable_in(sideCl);
  Literal* lmLit1 = best2.first.lit();
  Literal* lmLit2 = best2.second.lit();

  static vvector<BwSimplificationRecord> simplificationsStorage;
  ASS_EQ(simplificationsStorage.size(), 0);

  if (!lmLit1->isEquality() || !lmLit1->isPositive()) {
    // lmLit1 is not a positive equality, so we don't need to check the other one
    performWithQueryLit(sideCl, lmLit1, simplificationsStorage);
  } else if (!lmLit2->isEquality() || !lmLit2->isPositive()) {
    performWithQueryLit(sideCl, lmLit2, simplificationsStorage);
  } else {
    // both are positive equalities so we need to check both of them
    performWithQueryLit(sideCl, lmLit1, simplificationsStorage);
    performWithQueryLit(sideCl, lmLit2, simplificationsStorage);
  }

  simplifications = getPersistentIterator(getSTLIterator(simplificationsStorage.begin(), simplificationsStorage.end()));
  simplificationsStorage.clear();
}  // perform


void BackwardSubsumptionDemodulation::performWithQueryLit(Clause* sideCl, Literal* candidateQueryLit, vvector<BwSimplificationRecord>& simplifications)
{
  //   sideCl
  // vvvvvvvvvv
  //
  // l = r \/ C      CΘ \/ L[lΘ] \/ D
  // --------------------------------
  //       CΘ \/ L[rΘ] \/ D

#if VDEBUG
  // make sure DuplicateLiteralRemovalISE has been run on this
  DHSet<Literal*> lits;
  for (unsigned i = 0; i < sideCl->length(); ++i) {
    ALWAYS(lits.insert((*sideCl)[i]));
  }
#endif

  bool mustPredInit = false;
  bool mustPredActive = false;
  unsigned mustPred;

  SLQueryResultIterator rit = _index->getInstances(candidateQueryLit, false, false);
  while (rit.hasNext()) {
    SLQueryResult qr = rit.next();
    Clause* candidate = qr.clause;

    // not enough literals to fit match and rewritten literal (performance)
    if (sideCl->length() > candidate->length()) {
      continue;
    }

    // this is impossible
    // (if it triggers, then skip the candidate. SD with twice the same clause is impossible. even if it were, FSD should have dealt with it.)
    ASS_NEQ(sideCl, candidate);

    if (candidate->hasAux()) {
      continue;  // we've already checked this premise
    }
    candidate->setAux(nullptr);

    if (!ColorHelper::compatible(sideCl->color(), candidate->color())) {
      continue;
    }

    RSTAT_CTR_INC("bsd 0 candidates");

    // Here we pick one literal header of the base clause and make sure that
    // every instance clause has it
    //
    // Possibilities to consider:
    // 1. Choose one that is not a positive equality, the other clause must contain it.
    // 2. Choose two positive equalities, the other clause must contain at least one of them. (but those are indistinguishable by literal header)
    // 3. If it's a two-literal clause where the only thing left here is the positive equality, we cannot (and should not) exclude anything with this check.
    //
    // Case A: candidateQueryLit is not a positive equality.
    // - there is at least one positive equality in the remaining literals
    // - we need to skip one positive equality for the "mustPred" check.
    // Case B: candidateQueryLit is a positive equality.
    // - in this case, there is another positive equality in sideCl due to selection of the candidateQueryLit.
    // - Case B.1: BSD where candidateQueryLit is the rewriting equality:
    //             => any of the others can be chosen as mustPred
    //             (this case doesn't really matter since it will be found by the other call to this function; with the other candidateQueryLit.)
    //   Case B.2: BSD where candidateQueryLit is not the rewriting equality:
    //             => we must skip one positive equality for the "mustPred" check
    //
    // Summary: must skip one positive equality in the remaining literals for this "mustPred" check.
    if (!mustPredInit) {
      unsigned const positiveEqualityHeader = 1;
#if VDEBUG
      // To verify the hard-coded value of positiveEqualityHeader
      Literal* posEq = Literal::createEquality(true, TermList(0, false), TermList(1, false), AtomicSort::defaultSort());
      ASS_EQ(posEq->header(), positiveEqualityHeader);
#endif
      unsigned numPosEqs = 0;
      //since the base clause has at least two children, this will always
      //contain an existing literal header after the loop
      mustPred = 0;  // header value 0 means positive equality
      for (unsigned bi = 0; bi < sideCl->length(); ++bi) {
        Literal* blit = (*sideCl)[bi];
        if (blit == candidateQueryLit) {
          continue;
        }
        // only count in the other literals (see case B.2)
        if (blit->isPositive() && blit->isEquality()) {
          ++numPosEqs;
        }
        unsigned pred = blit->header();
        if (pred > mustPred) {
          mustPred = pred;
        }
      }
      if (mustPred == positiveEqualityHeader) {
        // for positive equality we need to have skipped at least in the remaining literals
        mustPredActive = (numPosEqs >= 2);
      } else {
        mustPredActive = true;
      }
    }
    if (mustPredActive) {
      bool haveMustPred = false;
      for (unsigned ii = 0; ii < candidate->length(); ++ii) {
        Literal* lit = (*candidate)[ii];
        if (lit == qr.literal) {
          continue;
        }
        unsigned pred = lit->header();
        if (pred == mustPred) {
          haveMustPred = true;
          break;
        }
      }
      if (!haveMustPred) {
        continue;
      }
    }
    RSTAT_CTR_INC("bsd 1 mustPred survivors");

    simplifyCandidate(sideCl, candidate, simplifications);
  }
}  // performWithQueryLit


/// Handles the matching part.
/// Returns true iff the main premise has been simplified.
bool BackwardSubsumptionDemodulation::simplifyCandidate(Clause* sideCl, Clause* mainCl, vvector<BwSimplificationRecord>& simplifications)
{
    static vvector<LiteralList*> alts;

    alts.clear();
    alts.resize(sideCl->length(), LiteralList::empty());

    unsigned baseLitsWithoutAlternatives = 0;
    for (unsigned bi = 0; bi < sideCl->length(); ++bi) {
      Literal* baseLit = (*sideCl)[bi];

      for (unsigned ii = 0; ii < mainCl->length(); ++ii) {
        Literal* instLit = (*mainCl)[ii];
        if (MatchingUtils::match(baseLit, instLit, false)) {
          LiteralList::push(instLit, alts[bi]);
        }
      }  // for(ii)

      if (LiteralList::isEmpty(alts[bi])) {
        // baseLit does not have any suitable alternative at all!
        //
        // If there are base literals without any suitable alternatives:
        // 1. If there is only one literal without alternative and it is a positive equality,
        //    then it might still be possible to get an SD inference by choosing this literal
        //    as equality for demodulation.
        // 2. If there is a literal without alternative but it is not a positive equality,
        //    then it is impossible to get an SD inference.
        // 3. If there are two literals without alternatives, then it is impossible as well.
        //
        // (This check exists purely for performance reasons.
        // MLMatcher would exclude cases 2 and 3 as well, but with additional overhead.)
        baseLitsWithoutAlternatives += 1;
        if (baseLitsWithoutAlternatives == 1) {
          if (!baseLit->isEquality() || !baseLit->isPositive()) {
            // We are in case 2 => skip
            baseLitsWithoutAlternatives += 1;  // a hack so we don't need another variable to check whether to skip below (in other words, merge case 2 into case 3 for purpose of the "if" below)
            break;
          }
        } else {
          // We are in case 3 => skip
          ASS_G(baseLitsWithoutAlternatives, 1);
          break;
        }
      }
    }  // for(bi)

    // Ensure cleanup of LiteralLists
    ON_SCOPE_EXIT({
      for (LiteralList* ll : alts) {
        LiteralList::destroy(ll);
      }
    });

    // Skip due to missing alternatives? (see comment above, "baseLit does not have any suitable alternative")
    if (baseLitsWithoutAlternatives > 1) {
      RSTAT_CTR_INC("BSD, skipped candidate main premise due to baseLitsWithoutAlternatives");
      return false;
    }

    ASS_LE(baseLitsWithoutAlternatives, 1);
    ASS_EQ(sideCl->length(), alts.size());

    static MLMatcherSD matcher;
    matcher.init(sideCl, mainCl, alts.data());

    static unsigned const maxMatches =
      getOptions().backwardSubsumptionDemodulationMaxMatches() == 0
      ? std::numeric_limits<decltype(maxMatches)>::max()
      : getOptions().backwardSubsumptionDemodulationMaxMatches();

    unsigned numMatches = 0;
    for (; numMatches < maxMatches; ++numMatches) {
      if (!matcher.nextMatch()) {
        break;
      }

      Clause* replacement = nullptr;
      if (rewriteCandidate(sideCl, mainCl, matcher, replacement)) {
        RSTAT_MCTR_INC("BSD, successes by MLMatch", numMatches + 1);  // +1 so it fits with the previous output
        simplifications.emplace_back(mainCl, replacement);
        return true;
      }
    }  // for (numMatches)

    if (numMatches > 0) {
      RSTAT_CTR_INC("BSD, MLMatch but no subsumption demodulation");
    }

    return false;
}  // simplifyCandidate


/// Handles the rewriting part.
/// Returns true iff the main premise has been simplified.
bool BackwardSubsumptionDemodulation::rewriteCandidate(Clause* sideCl, Clause* mainCl, MLMatcherSD const& matcher, Clause*& replacement)
{
  Ordering const& ordering = _salg->getOrdering();

  Literal* eqLit = matcher.getEqualityForDemodulation();
  if (!eqLit) {
    // eqLit == nullptr means that the whole side premise can be instantiated to some subset of the candidate,
    // i.e., we have subsumption.
#if VDEBUG && BSD_VDEBUG_REDUNDANCY_ASSERTIONS
    if (getOptions().literalComparisonMode() != Options::LiteralComparisonMode::REVERSE) {
      OverlayBinder tmpBinder;
      matcher.getBindings(tmpBinder.base());
      ASS(SDHelper::substClauseIsSmallerOrEqual(sideCl, tmpBinder, mainCl, ordering));
    }
#endif
    ASS(replacement == nullptr);
    env.statistics->backwardSubsumed++;
    return true;
  }
  ASS(eqLit->isEquality());
  ASS(eqLit->isPositive());

  TermList const eqSort = SortHelper::getEqualityArgumentSort(eqLit);

  Ordering::Result const eqArgOrder = ordering.getEqualityArgumentOrder(eqLit);
  bool const preordered = (eqArgOrder == Ordering::LESS) || (eqArgOrder == Ordering::GREATER);
  if (_preorderedOnly && !preordered) {
    return false;
  }

  // isMatched[i] is true iff (*mainCl)[i] is matched by some literal in sideCl (other than eqLit)
  static vvector<bool> isMatched;
  matcher.getMatchedAltsBitmap(isMatched);

  static OverlayBinder binder;
  binder.clear();
  matcher.getBindings(binder.base());

  // NOTE: for explanation see comments in ForwardSubsumptionDemodulation::perform
  static vvector<TermList> lhsVector;
  lhsVector.clear();
  {
    TermList t0 = *eqLit->nthArgument(0);
    TermList t1 = *eqLit->nthArgument(1);

    OverlayBinder::UnboundVariableOffsetApplicator applicator(binder, mainCl->maxVar()+1);
    switch (eqArgOrder) {
      case Ordering::INCOMPARABLE:
        ASS(!_preorderedOnly);  // would've skipped earlier already

        // If t0S does not contain all variables of t1S,
        // then t0Θ cannot be larger than t1Θ, where Θ is the final substitution (and S is the partial substitution after MLMatch).
        // (note this doesn't hold for occurrences: consider t0 = f(f(x,c)), t1 = f(x,x), θ = { x -> c }, then t0θ > t1θ)
        if (termContainsAllVariablesOfOtherUnderSubst(t0, t1, applicator)) {
          lhsVector.push_back(t0);
        }
        if (termContainsAllVariablesOfOtherUnderSubst(t1, t0, applicator)) {
          lhsVector.push_back(t1);
        }

        RSTAT_MCTR_INC("BSD, lhsVector.size() when INCOMPARABLE", lhsVector.size());
        break;
      case Ordering::GREATER:
      case Ordering::GREATER_EQ:
        ASS(termContainsAllVariablesOfOtherUnderSubst(t0, t1, applicator));
        lhsVector.push_back(t0);
        break;
      case Ordering::LESS:
      case Ordering::LESS_EQ:
        ASS(termContainsAllVariablesOfOtherUnderSubst(t1, t0, applicator));
        lhsVector.push_back(t1);
        break;
      case Ordering::EQUAL:
        // This case may happen due to the partial substitution from the MLMatcher
        RSTAT_CTR_INC("BSD, terms equal after partial substitution");
        break;
      default:
        ASSERTION_VIOLATION;
    }
  }

  if (lhsVector.size() == 0) {
    RSTAT_CTR_INC("BSD, skipped match due to no LHS term candidates");
    return false;
  }



  static DHSet<TermList> attempted;  // Terms we already attempted to demodulate
  attempted.reset();

  for (unsigned dli = 0; dli < mainCl->length(); ++dli) {
    Literal* dlit = (*mainCl)[dli];  // literal to be demodulated

    // Only demodulate in literals that are not matched by the subsumption check
    if (isMatched[dli]) {
      continue;
    }

    // TODO higher-order support not yet implemented; see forward demodulation
    //      (maybe it's enough to just use the different iterator)
    ASS(!env.options->combinatorySup());
    NonVariableNonTypeIterator nvi(dlit);
    while (nvi.hasNext()) {
      TermList lhsS = nvi.next();  // named 'lhsS' because it will be matched against 'lhs'

      if (!attempted.insert(lhsS)) {
        // We have already tried to demodulate the term lhsS and did not
        // succeed (otherwise we would have returned from the function).
        // If we have tried the term lhsS, we must have tried to
        // demodulate also its subterms, so we can skip them too.
        nvi.right();
        continue;
      }

      TermList const lhsSSort = SortHelper::getTermSort(lhsS, dlit);

      ASS_LE(lhsVector.size(), 2);
      for (TermList lhs : lhsVector) {
        TermList rhs = EqHelper::getOtherEqualitySide(eqLit, lhs);

#if VDEBUG
        if (preordered) {
          if (eqArgOrder == Ordering::LESS) {
            ASS_EQ(rhs, *eqLit->nthArgument(0));
          } else {
            ASS_EQ(rhs, *eqLit->nthArgument(1));
          }
        }
#endif

        binder.reset();  // reset binder to state after subsumption check
        if (!MatchingUtils::matchTerms(lhs, lhsS, binder)) {
          continue;
        }
        // If lhs is a variable, we need to match its sort separately.
        if (lhs.isVar() && !MatchingUtils::matchTerms(eqSort, lhsSSort, binder)) {
          continue;
        }

#if VDEBUG
        {
          // There can be no unbound variables at this point;
          // otherwise we would have excluded the LHS already
          // in the ordering pre-check above
          auto mclVarIt = sideCl->getVariableIterator();  // includes vars in rhs
          while (mclVarIt.hasNext()) {
            unsigned int var = mclVarIt.next();
            ASS(binder.isBound(var));
          }
        }
#endif

        TermList rhsS = binder.applyTo(rhs);
        ASS_EQ(lhsS, binder.applyTo(lhs));

        if (!preordered && ordering.compare(lhsS, rhsS) != Ordering::GREATER) {
          continue;
        }

        // NOTE: see comments in ForwardSubsumptionDemodulation::perform for explanation
        if (!_allowIncompleteness) {
          if (!dlit->isEquality()) {
            // non-equality literals are always larger than equality literals ==>  eqLitS < dlit
            ASS_EQ(ordering.compare(binder.applyTo(eqLit), dlit), Ordering::LESS);
            goto isRedundant;
          }
          if (lhsS != *dlit->nthArgument(0) && lhsS != *dlit->nthArgument(1)) {
            // lhsS appears as argument to some function, e.g. f(lhsS) = t
            // from subterm property of simplification ordering we know that lhsS < f(lhsS) and thus eqLitS < dlit
            ASS_EQ(ordering.compare(binder.applyTo(eqLit), dlit), Ordering::LESS);
            goto isRedundant;
          }
          // Now we are in the following situation:
          //
          //      eqLit              dlit
          //    vvvvvvvvv          vvvvvvvvv
          //    lhs = rhs \/ C     lhsS ?= t \/ CΘ \/ D
          //   ------------------------------------------
          //             rhsS ?= t \/ CΘ \/ D
          //
          //  where "?=" is either "=" or "≠".
          TermList t = EqHelper::getOtherEqualitySide(dlit, lhsS);
          if (t == rhsS) {
            ASS(eqLit->isPositive());
            if (dlit->isPositive()) {
              // in this case, eqLitS == dlit; and we have subsumption
              ASS_EQ(binder.applyTo(eqLit), dlit);  // eqLitS == dlit
#if VDEBUG && BSD_VDEBUG_REDUNDANCY_ASSERTIONS
              if (getOptions().literalComparisonMode() != Options::LiteralComparisonMode::REVERSE) {
                ASS(SDHelper::substClauseIsSmallerOrEqual(sideCl, binder, mainCl, ordering));
              }
#endif
              ASS(replacement == nullptr);
              env.statistics->backwardSubsumed++;
              return true;
            } else {
              // Here, we have subsumption resolution
              ASS_EQ(binder.applyTo(eqLit), Literal::complementaryLiteral(dlit));  // ¬eqLitS == dlit
              ASS_EQ(ordering.compare(binder.applyTo(eqLit), dlit), Ordering::GREATER);  // L > ¬L
              ASS(SDHelper::checkForSubsumptionResolution(mainCl, SDClauseMatches{sideCl,LiteralMiniIndex{mainCl}}, dlit));
              replacement = SDHelper::generateSubsumptionResolutionClause(mainCl, dlit, sideCl);
#if VDEBUG && BSD_VDEBUG_REDUNDANCY_ASSERTIONS
              if (getOptions().literalComparisonMode() != Options::LiteralComparisonMode::REVERSE) {
                // Note that mclθ < cl does not always hold here,
                // but we don't need it to ensure redundancy of cl
                // because cl is already entailed by replacement alone
                ASS(SDHelper::clauseIsSmaller(replacement, mainCl, ordering));
              }
#endif
              env.statistics->backwardSubsumptionResolution++;
              return true;
            }
          }
          Ordering::Result r_cmp_t = ordering.compare(rhsS, t);
          ASS_NEQ(r_cmp_t, Ordering::LESS_EQ);  // NOTE: LESS_EQ doesn't seem to occur in the code currently. It is unclear why the ordering is not simplified to LESS, EQUAL and GREATER.
          if (r_cmp_t == Ordering::LESS) {
            // rhsS < t implies eqLitS < dlit
            ASS_EQ(ordering.compare(binder.applyTo(eqLit), dlit), Ordering::LESS);
            goto isRedundant;
          }
          // We could not show redundancy with dlit alone,
          // so now we have to look at the other literals of the main premise
          Literal* eqLitS = Literal::createEquality(true, lhsS, rhsS, lhsSSort);
          ASS_EQ(eqLitS, binder.applyTo(eqLit));
          for (unsigned li2 = 0; li2 < mainCl->length(); li2++) {
            // skip dlit (already checked with r_cmp_t above) and matched literals (i.e., CΘ)
            if (dli != li2 && !isMatched[li2]) {
              Literal* lit2 = (*mainCl)[li2];
              if (ordering.compare(eqLitS, lit2) == Ordering::LESS) {
                // we found that eqLitS < lit2; and thus sideCl < mainCl => after inference, mainCl is redundant
                goto isRedundant;
              }
            }
          }
          // mainCl is not be redundant after the inference, possibly leading to incompleteness => skip
          RSTAT_CTR_INC("BSD, main premise not redundant");
          continue;
        }  // if (!_allowIncompleteness)
isRedundant:

#if VDEBUG && BSD_VDEBUG_REDUNDANCY_ASSERTIONS
        if (getOptions().literalComparisonMode() != Options::LiteralComparisonMode::REVERSE) {
          // Check mclΘ < cl.
          // This is not clear and might easily be violated if we have a bug above.
          if (!SDHelper::substClauseIsSmaller(sideCl, binder, mainCl, ordering)) {
            std::cerr << "BSD: redundancy violated!" << std::endl;
            std::cerr << "side: " << sideCl->toString() << std::endl;
            std::cerr << "main: " << mainCl->toString() << std::endl;
            std::cerr << "sideS < main required but it doesn't seem to be the case" << std::endl;
            ASSERTION_VIOLATION;
          }
        }
#endif

        /**
         * Step 4: found application of SD; now create the conclusion
         */
        Literal* newLit = EqHelper::replace(dlit, lhsS, rhsS);
        ASS_EQ(ordering.compare(lhsS, rhsS), Ordering::GREATER);
#if VDEBUG
        if (getOptions().literalComparisonMode() != Options::LiteralComparisonMode::REVERSE) {
          // blows up with "-lcm reverse"; but the same thing happens with normal demodulation, so this might be intended?
          ASS_EQ(ordering.compare(dlit, newLit), Ordering::GREATER);
        }
#endif

        if (EqHelper::isEqTautology(newLit)) {
          env.statistics->backwardSubsumptionDemodulationsToEqTaut++;
          ASS(replacement == nullptr);
          return true;
        }

        Clause* newCl = new(mainCl->length()) Clause(mainCl->length(),
            SimplifyingInference2(InferenceRule::BACKWARD_SUBSUMPTION_DEMODULATION, mainCl, sideCl));

        for (unsigned i = 0; i < mainCl->length(); ++i) {
          if (i == dli) {
            (*newCl)[i] = newLit;
          } else {
            (*newCl)[i] = (*mainCl)[i];
          }
        }

        env.statistics->backwardSubsumptionDemodulations++;

        replacement = newCl;

#if BSD_LOG_INFERENCES
        env.beginOutput();
        env.out() << "\% Begin Inference \"BSD-" << newCl->number() << "\"\n";
        env.out() << "\% eqLit: " << eqLit->toString() << "\n";
        env.out() << "\% eqLitS: " << binder.applyTo(eqLit)->toString() << "\n";
        env.out() << "\% dlit: " << dlit->toString() << "\n";
        // env.out() << "\% numMatches+1: success at match #" << (numMatches+1) << "\n";
        TPTPPrinter tptp;
        // NOTE: do not output the splitLevels here, because those will be set for newCl only later
        tptp.printWithRole("side_premise", "hypothesis", sideCl, false);
        tptp.printWithRole("main_premise", "hypothesis", mainCl, false);
        tptp.printWithRole("conclusion  ", "conjecture", newCl, false);
        // TODO: Some problems (seems to be only the CSR category; it happens, e.g., in CSR104+4)
        //       use integer constants as sort $i but vampire parses them as $int when using tff.
        //       For these formulas we should use fof, then it works again.
        //       Problem: how to detect that situation??
        //       probably if the input only contains FOF and no TFF
        // TODO: Also don't output type defs for $$false and $$true, see problem SYO091^5.p
        env.out() << "\% End Inference \"BSD-" << newCl->number() << "\"" << std::endl;
        env.endOutput();
#endif

#if VDEBUG && BSD_VDEBUG_REDUNDANCY_ASSERTIONS
        if (getOptions().literalComparisonMode() != Options::LiteralComparisonMode::REVERSE) {  // see note above
          // Check newCl < mainCl.
          ASS(SDHelper::clauseIsSmaller(newCl, mainCl, ordering));
        }
#endif

        return true;
      }  // for (lhs)
    }  // while (nvi.hasNext())
  }  // for (dli)

  return false;
}  // rewriteCandidate


}
