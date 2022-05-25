/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "ForwardSubsumptionDemodulation.hpp"
#include "SubsumptionDemodulationHelper.hpp"

#include "Debug/RuntimeStatistics.hpp"
#include "Indexing/Index.hpp"
#include "Indexing/IndexManager.hpp"
#include "Indexing/LiteralIndex.hpp"
#include "Indexing/LiteralMiniIndex.hpp"
#include "Kernel/ColorHelper.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/MLMatcherSD.hpp"
#include "Kernel/Matcher.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/OperatorType.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Term.hpp"
#include "Lib/ScopeGuard.hpp"
#include "Lib/STL.hpp"
#include "Lib/STLAllocator.hpp"
#include "Saturation/SaturationAlgorithm.hpp"
#include "Shell/TPTPPrinter.hpp"
#include <array>
#include <unordered_map>
#include <unordered_set>
#include <vector>

using namespace Kernel;
using namespace Lib;
using namespace Inferences;
using namespace Saturation;


void ForwardSubsumptionDemodulation::attach(SaturationAlgorithm* salg)
{
  CALL("ForwardSubsumptionDemodulation::attach");
  ForwardSimplificationEngine::attach(salg);

  _index.request(salg->getIndexManager(), FSD_SUBST_TREE);

  _preorderedOnly = false;
  _allowIncompleteness = false;

  if (_doSubsumption) {
    _unitIndex.request(salg->getIndexManager(), SIMPLIFYING_UNIT_CLAUSE_SUBST_TREE);
  }
}


void ForwardSubsumptionDemodulation::detach()
{
  CALL("ForwardSubsumptionDemodulation::detach");
  _index.release();
  ForwardSimplificationEngine::detach();
}


bool ForwardSubsumptionDemodulation::perform(Clause* cl, Clause*& replacement, ClauseIterator& premises)
{
  CALL("ForwardSubsumptionDemodulation::perform");

  //                        cl
  //                 vvvvvvvvvvvvvvvv
  //     mcl       matched      /-- only look for a term to demodulate in this part!
  // vvvvvvvvvv      vv    vvvvvvvvvv
  // eqLit                  dlit
  // vvvvv                 vvvvv
  //
  // l = r \/ C      CΘ \/ L[lΘ] \/ D
  // --------------------------------
  //       CΘ \/ L[rΘ] \/ D
  //
  // where
  // 1. lΘ > rΘ, and
  // 2. l = r \/ C  <  CΘ \/ L[lΘ] \/ D   (to ensure the right premise is redundant after the inference)
  //
  // For condition 2, we check that l = r < M for some M in L \/ D.

  TimeCounter const tc(TC_FORWARD_SUBSUMPTION_DEMODULATION);

  Ordering const& ordering = _salg->getOrdering();

  // Discard all previous aux values (so after this, hasAux() returns false for any clause).
  Clause::requestAux();
  ON_SCOPE_EXIT({ Clause::releaseAux(); });

  // Subsumption by unit clauses
  if (_doSubsumption) {
    for (unsigned sqli = 0; sqli < cl->length(); ++sqli) {
      SLQueryResultIterator rit = _unitIndex->getGeneralizations((*cl)[sqli], false, false);
      while (rit.hasNext()) {
        Clause* premise = rit.next().clause;

        if (premise->hasAux()) {
          continue;  // we've already checked this premise
        }
        premise->setAux(nullptr);

        if (!ColorHelper::compatible(cl->color(), premise->color())) {
          continue;
        }

        premises = pvi(getSingletonIterator(premise));
        env.statistics->forwardSubsumed++;
        return true;
      }
    }
  }

  LiteralMiniIndex const cl_miniIndex(cl);

  unsigned int const cl_maxVar = cl->maxVar();

  for (unsigned sqli = 0; sqli < cl->length(); ++sqli) {
    Literal* subsQueryLit = (*cl)[sqli];  // this literal is only used to query the subsumption index

    /**
     * Step 1: find candidate clauses for subsumption
     */
    SLQueryResultIterator rit = _index->getGeneralizations(subsQueryLit, false, false);
    while (rit.hasNext()) {
      SLQueryResult res = rit.next();
      Clause* mcl = res.clause;  // left premise of FSD

      ASS_NEQ(cl, mcl);  // this can't happen because cl isn't in the index yet

      // (this check exists only to improve performance and does not affect correctness)
      if (mcl->hasAux()) {
        // we've already checked this clause
        continue;
      }
      mcl->setAux(nullptr);

      // No multiset match possible if base is longer than instance
      // (this check exists only to improve performance and does not affect correctness)
      if (mcl->length() > cl->length()) {
        continue;
      }

      if (!ColorHelper::compatible(cl->color(), mcl->color())) {
        continue;
      }

      /**
       * Step 2: choose a positive equality in mcl to use for demodulation and try to instantiate the rest to some subset of cl
       */
      static vvector<LiteralList*> alts;
      alts.clear();
      alts.reserve(mcl->length());
      ASS_EQ(alts.size(), 0);
      unsigned baseLitsWithoutAlternatives = 0;
      for (unsigned mi = 0; mi < mcl->length(); ++mi) {
        Literal* baseLit = (*mcl)[mi];

        LiteralMiniIndex::InstanceIterator instIt(cl_miniIndex, baseLit, false);

        if (!instIt.hasNext()) {
          // baseLit does not have any suitable alternative at all!
          //
          // If there are base literals without any suitable alternatives:
          // 1. If there is only one literal without alternative and it is a positive equality,
          //    then it might still be possible to get an FSD inference by choosing this literal
          //    as equality for demodulation.
          // 2. If there is a literal without alternative but it is not a positive equality,
          //    then it is impossible to get an FSD inference.
          // 3. If there are two literals without alternatives, then it is impossible as well.
          //
          // (This check exists purely for performance reasons.
          // MLMatcher would exclude cases 2 and 3 as well, but with additional overhead.)
          //
          // Note that we do not have to check whether mcl contains a positive equality at all.
          // There are two useful configurations to consider:
          // a. We do not want to do forward subsumption here and are using the FSD index.
          //    The FSD index only contains clauses that have a positive equality, and mcl is chosen from this index.
          // b. We do forward subsumption as part of FSD and are using the (adjusted) FS index.
          //    In this case we do not want to exclude an mcl without positive equality anyways.
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

        LiteralList* l = LiteralList::empty();
        while (instIt.hasNext()) {
          Literal* matched = instIt.next();
          LiteralList::push(matched, l);
        }
        alts.push_back(l);
      }

      // Ensure cleanup of LiteralLists
      ON_SCOPE_EXIT({
        for (LiteralList* ll : alts) {
          LiteralList::destroy(ll);
        }
      });

      // Skip due to missing alternatives? (see comment above, "baseLit does not have any suitable alternative")
      if (baseLitsWithoutAlternatives > 1) {
        RSTAT_CTR_INC("FSD, skipped side premise due to baseLitsWithoutAlternatives");
        continue;
      }

      ASS_EQ(mcl->length(), alts.size());

      static MLMatcherSD matcher;
      matcher.init(mcl, cl, alts.data());

      static unsigned const maxMatches =
        getOptions().forwardSubsumptionDemodulationMaxMatches() == 0
        ? std::numeric_limits<decltype(maxMatches)>::max()
        : getOptions().forwardSubsumptionDemodulationMaxMatches();

      unsigned numMatches = 0;
      for (; numMatches < maxMatches; ++numMatches) {
        if (!matcher.nextMatch()) {
          break;
        }

        Literal* eqLit = matcher.getEqualityForDemodulation();
        if (!eqLit) {
          // eqLit == nullptr means that the whole of mcl can be instantiated to some subset of cl,
          // i.e., cl is subsumed by mcl.
          //
          // Note that we should always apply Forward Subsumption if possible,
          // because it is a deletion rule; and Forward Subsumption should be performed before FSD.
#if VDEBUG && FSD_VDEBUG_REDUNDANCY_ASSERTIONS
          if (getOptions().literalComparisonMode() != Options::LiteralComparisonMode::REVERSE) {
            OverlayBinder tmpBinder;
            matcher.getBindings(tmpBinder.base());
            ASS(SDHelper::substClauseIsSmallerOrEqual(mcl, tmpBinder, cl, ordering));
          }
#endif
          ASS(replacement == nullptr);
          premises = pvi(getSingletonIterator(mcl));
          env.statistics->forwardSubsumed++;
          return true;
        }
        ASS(eqLit->isEquality());
        ASS(eqLit->isPositive());

        TermList const eqSort = SortHelper::getEqualityArgumentSort(eqLit);

        Ordering::Result const eqArgOrder = ordering.getEqualityArgumentOrder(eqLit);
        bool const preordered = (eqArgOrder == Ordering::LESS) || (eqArgOrder == Ordering::GREATER);
        if (_preorderedOnly && !preordered) {
          continue;
        }

        // isMatched[i] is true iff (*cl)[i] is matched my some literal in mcl (without eqLit)
        static vvector<bool> isMatched;
        matcher.getMatchedAltsBitmap(isMatched);

        static OverlayBinder binder;
        binder.clear();
        matcher.getBindings(binder.base());

        /**
         * Step 3: now we try to demodulate some term in an unmatched literal with eqLit.
         *
         * IMPORTANT: only look at literals that are not being matched to mcl (the rule is unsound otherwise)!
         *
         *       mcl                cl
         *   vvvvvvvvvv      vvvvvvvvvvvvvvvv
         *   eqLit         matched      /-- only look for a term to demodulate in this part!
         *   vvvvv           vv    vvvvvvvvvv
         *   l = r \/ C      CΘ \/ L[lΘ] \/ D
         *   --------------------------------
         *         CΘ \/ L[rΘ] \/ D
         *
         */

        // Select candidate lhs of eqLit for demodulation.
        // Must be larger than the rhs after substitution.
        //
        // Three possible outcomes:
        // 1. No LHS (if INCOMPARABLE and no side contains all variables of the other side)
        // 2. One LHS (oriented, or INCOMPARABLE with exactly one variable-free side)
        // 3. Two LHSs (INCOMPARABLE and same variables)
        static vvector<TermList> lhsVector;
        lhsVector.clear();
        {
          TermList t0 = *eqLit->nthArgument(0);
          TermList t1 = *eqLit->nthArgument(1);

          // Before comparing the variable occurrences in the terms (to select
          // a suitable demodulation LHS), we have to apply the partial
          // substitution arising from the MLMatch.  This is because variables
          // that are disjoint before the partial substitution might be the
          // same after applying the substitution; due to the instantiation of
          // other literals in the subsumption part.
          //
          // However, we must be careful to separate the variables coming from
          // mcl (the domain of the substitution) and the variables coming from
          // cl (in the range of the substitution).
          // In particular, any variables in mcl that are still unbound in the
          // partial substitution must be mapped to some other variables that
          // do not occur in cl.
          //
          // Note that in the final substitution all variables in mcl must be
          // bound: if any variables of mcl are still unbound in the final
          // substitution, they must occur only in rhs (because lhs is matched
          // against lhsS, inducing bindings for all of its variables; and all
          // other literals were already matched in the partial substitution).
          // But if a variable occurs only in rhs after the final substitution,
          // then the ordering result for lhs/rhs is INCOMPARABLE and we cannot
          // perform the inference.  We filter these cases already here by
          // checking 'containsAllVariableOccurrencesOf'.
          //
          // We ensure that unbound variables are disjoint from variables in cl
          // by shifting them by 'cl->maxVar()+1'.

#if 0
          // Additional ordering check after the partial substitution.
          // Problem: fills up term sharing structure with temporary terms.
          // Currently there is no way to compare terms under a substitution without materializing them,
          // and non-shared terms cannot be compared (triggers assertions in at least KBO).
          // To fix this, it would be nice to have a function such as
          //    Ordering::compare(TermList t1, std::function<TermList(unsigned)> theta1,
          //                      TermList t2, std::function<TermList(unsigned)> theta2)
          // which compares terms under the given substitution.
          // (if we're fine with moving the ordering implementation into headers,
          //  we can do this without code duplication and no performance penalty for the currently supported common case.)

          TermList t0S = binder.applyWithUnboundVariableOffsetTo(t0, cl_maxVar+1, false);
          TermList t1S = binder.applyWithUnboundVariableOffsetTo(t1, cl_maxVar+1, false);
          Ordering::Result eqArgOrderS = ordering.compare(t0S, t1S);
          if (eqArgOrder == Ordering::INCOMPARABLE && eqArgOrderS != Ordering::INCOMPARABLE) {
            RSTAT_CTR_INC("FSD, ordered after partial substitution");
          }
#else
          // No additional ordering check.
          // But note that we still need to compare the variable sets of the substituted terms below.
          Ordering::Result eqArgOrderS = eqArgOrder;
#endif
          OverlayBinder::UnboundVariableOffsetApplicator applicator(binder, cl_maxVar+1);
          switch (eqArgOrderS) {
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

              RSTAT_MCTR_INC("FSD, lhsVector.size() when INCOMPARABLE", lhsVector.size());
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
              RSTAT_CTR_INC("FSD, terms equal after partial substitution");
              break;
            default:
              ASSERTION_VIOLATION;
          }
        }

        if (lhsVector.size() == 0) {
          RSTAT_CTR_INC("FSD, skipped match due to no LHS term candidates");
          continue;
        }

        static DHSet<TermList> attempted;  // Terms we already attempted to demodulate
        attempted.reset();

        for (unsigned dli = 0; dli < cl->length(); ++dli) {
          Literal* dlit = (*cl)[dli];  // literal to be demodulated

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
                auto mclVarIt = mcl->getVariableIterator();  // includes vars in rhs
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

              // Redundancy Check
              //
              // FSD is a simplification rule, so we want the simplified
              // premise (the right premise, cl) to be redundant after the
              // inference.
              //
              // Three conditions need to be satisfied:
              // 1. The premises (cl, mcl) must logically entail the conclusion,
              // 2. cl must be larger than the conclusion, and
              // 3. cl must be larger than the left premise mcl
              //    (to be completely precise, after applying the substitution Θ to mcl, i.e. mclΘ < cl).
              //
              // Conditions 1 and 2 are quite obvious (for 2, recall that lhsS > rhsS).
              // Condition 3 will be checked now.
              //
              // For perfomance reasons, we do not perform an exact check of mclΘ < cl.
              // Using the notation from above, we already know that C <= CΘ for the subsumption part.
              // If we can show that lΘ=rΘ < L[lΘ] \/ D, we can conclude that lΘ=rΘ \/ CΘ < L[lΘ] \/ C \/ D.
              //                     ^^^^^   ^^^^^                            ^^^^^^^^^^^   ^^^^^^^^^^^^^^^
              // (variable names:    eqLitS   dlit                                mclΘ             cl      )
              //
              // It is enough to find one literal M in L[lΘ] \/ D such that lΘ=rΘ < M.
              //
              // As an optimization, we first try to choose L as M because there are
              // easy-to-check criteria whether lΘ=rΘ < L[lΘ] holds. This is true if
              // one of the following holds:
              // 1. L is not an equality (as non-equality literals are always larger than equalities).
              // 2. L is s[lΘ] = t with s[lΘ] ≠ lΘ.
              //    Then s[lΘ] > lΘ (due to the subterm property of simplification orderings),
              //    and thus s[lΘ]=t > lΘ=rΘ.  (multiset extension of ordering: { s[lΘ], t } > { s[lΘ] } > { lΘ, rΘ }, because s[lΘ] > lΘ > rΘ)
              // 3. L is lΘ = t, but t is larger that rΘ.
              // If all these checks fail, we try to find a literal M in D such that lΘ=rΘ < M.
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
                    // in this case, eqLitS == dlit; and forward subsumption should have deleted the right premise already
                    // Here, we have subsumption
                    ASS_EQ(binder.applyTo(eqLit), dlit);  // eqLitS == dlit
#if VDEBUG && FSD_VDEBUG_REDUNDANCY_ASSERTIONS
                    if (getOptions().literalComparisonMode() != Options::LiteralComparisonMode::REVERSE) {
                      ASS(SDHelper::substClauseIsSmallerOrEqual(mcl, binder, cl, ordering));
                    }
#endif
                    ASS(replacement == nullptr);
                    premises = pvi(getSingletonIterator(mcl));
                    env.statistics->forwardSubsumed++;
                    return true;
                  } else {
                    // Here, we have subsumption resolution
                    ASS_EQ(binder.applyTo(eqLit), Literal::complementaryLiteral(dlit));  // ¬eqLitS == dlit
                    ASS_EQ(ordering.compare(binder.applyTo(eqLit), dlit), Ordering::GREATER);  // L > ¬L
                    ASS(SDHelper::checkForSubsumptionResolution(cl, SDClauseMatches{mcl,cl_miniIndex}, dlit));
                    replacement = SDHelper::generateSubsumptionResolutionClause(cl, dlit, mcl);
#if VDEBUG && FSD_VDEBUG_REDUNDANCY_ASSERTIONS
                    if (getOptions().literalComparisonMode() != Options::LiteralComparisonMode::REVERSE) {
                      // Note that mclθ < cl does not always hold here,
                      // but we don't need it to ensure redundancy of cl
                      // because cl is already entailed by replacement alone
                      ASS(SDHelper::clauseIsSmaller(replacement, cl, ordering));
                    }
#endif
                    premises = pvi(getSingletonIterator(mcl));
                    env.statistics->forwardSubsumptionResolution++;
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
                // so now we have to look at the other literals of cl
                Literal* eqLitS = Literal::createEquality(true, lhsS, rhsS, lhsSSort);
                ASS_EQ(eqLitS, binder.applyTo(eqLit));
                for (unsigned li2 = 0; li2 < cl->length(); li2++) {
                  // skip dlit (already checked with r_cmp_t above) and matched literals (i.e., CΘ)
                  if (dli != li2 && !isMatched[li2]) {
                    Literal* lit2 = (*cl)[li2];
                    if (ordering.compare(eqLitS, lit2) == Ordering::LESS) {
                      // we found that eqLitS < lit2; and thus mcl < cl => after inference, cl is redundant
                      goto isRedundant;
                    }
                  }
                }
                // cl is not be redundant after the inference, possibly leading to incompleteness => skip
                RSTAT_CTR_INC("FSD, main premise not redundant");
                continue;
              }  // if (!_allowIncompleteness)
isRedundant:

#if VDEBUG && FSD_VDEBUG_REDUNDANCY_ASSERTIONS
              if (getOptions().literalComparisonMode() != Options::LiteralComparisonMode::REVERSE) {
                // Check mclΘ < cl.
                // This is not clear and might easily be violated if we have a bug above.
                if (!SDHelper::substClauseIsSmaller(mcl, binder, cl, ordering)) {
                  std::cerr << "FSD: redundancy violated!" << std::endl;
                  std::cerr << "mcl: " << mcl->toString() << std::endl;
                  std::cerr << " cl: " <<  cl->toString() << std::endl;
                  std::cerr << "mclS < cl required but it doesn't seem to be the case" << std::endl;
                  ASSERTION_VIOLATION;
                }
              }
#endif

              /**
               * Step 4: found application of FSD; now create the conclusion
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
                env.statistics->forwardSubsumptionDemodulationsToEqTaut++;
                premises = pvi(getSingletonIterator(mcl));
                replacement = nullptr;
                return true;
              }

              Clause* newCl = new(cl->length()) Clause(cl->length(),
                  SimplifyingInference2(InferenceRule::FORWARD_SUBSUMPTION_DEMODULATION, cl, mcl));

              for (unsigned i = 0; i < cl->length(); ++i) {
                if (i == dli) {
                  (*newCl)[i] = newLit;
                } else {
                  (*newCl)[i] = (*cl)[i];
                }
              }

              env.statistics->forwardSubsumptionDemodulations++;

              premises = pvi(getSingletonIterator(mcl));
              replacement = newCl;

#if FSD_LOG_INFERENCES
              env.beginOutput();
              env.out() << "\% Begin Inference \"FSD-" << newCl->number() << "\"\n";
              env.out() << "\% eqLit: " << eqLit->toString() << "\n";
              env.out() << "\% eqLitS: " << binder.applyTo(eqLit)->toString() << "\n";
              env.out() << "\% dlit: " << dlit->toString() << "\n";
              env.out() << "\% numMatches+1: success at match #" << (numMatches+1) << "\n";
              TPTPPrinter tptp;
              // NOTE: do not output the splitLevels here, because those will be set for newCl only later
              tptp.printWithRole("side_premise_mcl", "hypothesis", mcl,   false);
              tptp.printWithRole("main_premise_cl ", "hypothesis", cl,    false);
              tptp.printWithRole("conclusion      ", "conjecture", newCl, false);
              // TODO: Some problems (seems to be only the CSR category; it happens, e.g., in CSR104+4)
              //       use integer constants as sort $i but vampire parses them as $int when using tff.
              //       For these formulas we should use fof, then it works again.
              //       Problem: how to detect that situation??
              //       probably if the input only contains FOF and no TFF
              // TODO: Also don't output type defs for $$false and $$true, see problem SYO091^5.p
              env.out() << "\% End Inference \"FSD-" << newCl->number() << "\"" << std::endl;
              env.endOutput();
#endif

              RSTAT_MCTR_INC("FSD, successes by MLMatch", numMatches + 1);  // +1 so it fits with the previous output

#if VDEBUG && FSD_VDEBUG_REDUNDANCY_ASSERTIONS
              if (getOptions().literalComparisonMode() != Options::LiteralComparisonMode::REVERSE) {  // see note above
                // Check newCl < cl.
                // This is quite obvious, and there should be no problems with this.
                ASS(SDHelper::clauseIsSmaller(newCl, cl, ordering));
              }
#endif

              return true;
            }  // for (lhs)
          }  // while (nvi.hasNext())
        }  // for (dli)
      }  // for (numMatches)

      if (numMatches > 0) {
        RSTAT_CTR_INC("FSD, MLMatch but no FSD inference");
      }

    }  // while (rit.hasNext)
  }  // for (li)

  return false;
}
