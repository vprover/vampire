/*
 * File BackwardSubsumptionDemodulation.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions.
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide.
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
#include "Kernel/MLMatcher2.hpp"
#include "Kernel/Matcher.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Sorts.hpp"
#include "Kernel/Term.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/LiteralIndex.hpp"
#include "Indexing/LiteralMiniIndex.hpp"
#include "Indexing/IndexManager.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Statistics.hpp"

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


namespace {

// TODO: copied from LiteralIndex.cpp; should put this into a separate file.
//       and call it something more memorable, e.g. LeastMatchableLiteralRating ?
//       (and "least matchable" is more descriptive than "best", so rename the methods as well)
/**
 * A literal and its rating (for use in the subsumption index).
 * Ordered by ratings, breaking ties with the literal's pointer values.
 *
 * On the metric used to select the best literal:
 *
 *    val == #symbols - #distinct-variables
 *        == #non-variable-symbols + #variable-duplicates
 *
 * This value is the number of symbols that induce constraints for matching.
 * (Note that variables only induce constraints for instantiation on their repeated occurrences)
 * We want to maximize this value to have the most restricting literal,
 * so we get as little matches as possible (because the matches then have
 * to be passed to the MLMatcher which is expensive).
 */
class SubsRatedLiteral
{
  private:
    Literal* m_lit;
    unsigned m_val;

  public:
    SubsRatedLiteral(Literal* lit)
      : m_lit(lit), m_val(computeRating(lit))
    { }

    static unsigned computeRating(Literal* lit) { return lit->weight() - lit->getDistinctVars(); }

    Literal* lit() const { return m_lit; }

    bool operator<(SubsRatedLiteral const& other) const
    {
      return m_val < other.m_val || (m_val == other.m_val && m_lit < other.m_lit);
    }
    bool operator>(SubsRatedLiteral const& other) const { return other.operator<(*this); }
    bool operator<=(SubsRatedLiteral const& other) const { return !operator>(other); }
    bool operator>=(SubsRatedLiteral const& other) const { return !operator<(other); }
    bool operator==(SubsRatedLiteral const& other) const { return m_lit == other.m_lit; }
    bool operator!=(SubsRatedLiteral const& other) const { return !operator==(other); }

    static SubsRatedLiteral find_best_in(Clause* c)
    {
      SubsRatedLiteral best{(*c)[0]};
      for (unsigned i = 1; i < c->length(); ++i) {
        SubsRatedLiteral curr{(*c)[i]};
        if (curr > best) {
          best = curr;
        }
      }
      return best;
    }

    static std::pair<SubsRatedLiteral,SubsRatedLiteral> find_best2_in(Clause* c)
    {
      SubsRatedLiteral best{(*c)[0]};
      SubsRatedLiteral secondBest{(*c)[1]};
      if (secondBest > best) {
        std::swap(best, secondBest);
      }
      for (unsigned i = 2; i < c->length(); ++i) {
        SubsRatedLiteral curr{(*c)[i]};
        if (curr > best) {
          secondBest = best;
          best = curr;
        } else if (curr > secondBest) {
          secondBest = curr;
        }
      }
      ASS(best.lit() != secondBest.lit());
      ASS(best > secondBest);
      return {best, secondBest};
    }
};
}


void BackwardSubsumptionDemodulation::perform(Clause* cl, BwSimplificationRecordIterator& simplifications)
{
  // TODO rename cl -> sideCl because it is the side premise
  CALL("BackwardSubsumptionDemodulation::perform");
  ASSERT_VALID(*cl);

  TimeCounter tc(TC_BACKWARD_SUBSUMPTION_DEMODULATION);

  simplifications = BwSimplificationRecordIterator::getEmpty();

  if (cl->length() == 0) {
    // No BSD with empty clause possible
    ASSERTION_VIOLATION;  // wouldn't we just terminate in this case???  FIXME
    return;
  }

  if (cl->length() == 1) {
    // Handled by regular backward demodulation
    return;
  }

  bool hasPositiveEquality = false;
  for (unsigned i = 0; i < cl->length(); ++i) {
    Literal* lit = (*cl)[i];
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


  auto best2 = SubsRatedLiteral::find_best2_in(cl);
  Literal* lmLit1 = best2.first.lit();
  Literal* lmLit2 = best2.second.lit();

  v_vector<BwSimplificationRecord> simplificationsStorage;

  if (!lmLit1->isEquality() || lmLit1->isPositive()) {
    // lmLit1 is not a positive equality, so we don't need to check the other one
    perform2(cl, lmLit1, simplificationsStorage);
  } else if (!lmLit2->isEquality() || lmLit2->isPositive()) {
    perform2(cl, lmLit2, simplificationsStorage);
  } else {
    // both are positive equalities so we need to check both of them
    perform2(cl, lmLit1, simplificationsStorage);
    perform2(cl, lmLit2, simplificationsStorage);
  }

  // TODO: wrap simplificationsStorage in something like a persistent iterator (std::move the vector inside if needed)
  // simplifications = ;

}  // perform


void BackwardSubsumptionDemodulation::perform2(Clause* sideCl, Literal* candidateQueryLit, v_vector<BwSimplificationRecord>& simplifications)
{

  //                      candidate
  //                 vvvvvvvvvvvvvvvv
  //     cl        matched      /-- only look for a term to demodulate in this part!
  // vvvvvvvvvv      vv    vvvvvvvvvv
  // eqLit                  dlit
  // vvvvv                 vvvvv
  //
  // l = r \/ C      CΘ \/ L[lΘ] \/ D
  // --------------------------------
  //       CΘ \/ L[rΘ] \/ D

  /*
  ClauseList* subsumed=0;

  static DHSet<unsigned> basePreds;
  bool basePredsInit=false;
  bool mustPredInit=false;
  unsigned mustPred;
  */

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

    // TODO: maybe reinstate (some of?) these checks
    /*
    Literal* il=qr.clause;
    Literal* ilit=qr.literal;
    unsigned ilen=icl->length();

    RSTAT_CTR_INC("bsd 0 candidates");

    //here we pick one literal header of the base clause and make sure that
    //every instance clause has it
    if(!mustPredInit) {
      //since the base clause has at least two children, this will always
      //contain an existing literal header after the loop
      mustPred=0;
      for(unsigned bi=0;bi<clen;bi++) {
        if(bi==lmIndex) {
          continue;
        }
        unsigned pred=(*sideCl)[bi]->header();
        if(pred>mustPred) {
          mustPred=pred;
        }
      }
    }
    bool haveMustPred=false;
    for(unsigned ii=0;ii<ilen;ii++) {
      Literal* l=(*icl)[ii];
      if(l==ilit) {
        continue;
      }
      unsigned pred=l->header();
      if(pred==mustPred) {
        haveMustPred=true;
      }
    }
    if(!haveMustPred) {
      continue;
    }
    RSTAT_CTR_INC("bsd 1 mustPred survivors");

    //here we check that for every literal header in the base clause
    //there is a literal with the same header in the instance
    if(!basePredsInit) {
      basePredsInit=true;
      basePreds.reset();
      for(unsigned bi=0;bi<clen;bi++) {
        if(bi==lmIndex) {
          continue;
        }
        unsigned pred=(*sideCl)[bi]->header();
        basePreds.insert(pred);
      }
    }
    unsigned allowedMisses=ilen-clen; //how many times the instance may contain a predicate that is not in the base clause
    bool fail=false;
    for(unsigned ii=0;ii<ilen;ii++) {
      Literal* l=(*icl)[ii];
      if(l==ilit) {
        continue;
      }
      unsigned pred=l->header();
      if(!basePreds.find(pred)) {
        if(allowedMisses==0) {
          fail=true;
          break;
        }
        else {
          allowedMisses--;
        }
      }
    }
    if(fail) {
      continue;
    }

    RSTAT_CTR_INC("bsd 2 survived");
  */

    simplifyCandidate(sideCl, candidate, simplifications);

  }
}  // perform2


/// Handles the matching part.
/// Returns true iff the main premise has been simplified.
bool BackwardSubsumptionDemodulation::simplifyCandidate(Clause* sideCl, Clause* mainCl, v_vector<BwSimplificationRecord>& simplifications)
{
    static v_vector<LiteralList*> alts;

    alts.clear();
    alts.resize(sideCl->length(), LiteralList::empty());

    unsigned baseLitsWithoutAlternatives = 0;
    for (unsigned bi = 0; bi < sideCl->length(); ++bi) {
      Literal* baseLit = (*sideCl)[bi];

      // TODO: a minor optimization is possible here: we already know one instance of candidateQueryLit, namely qr.literal
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

    static MLMatcher2 matcher;
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
      if (simplifyCandidate2(sideCl, mainCl, matcher, replacement)) {
        RSTAT_MCTR_INC("BSD, successes by MLMatch", numMatches + 1);  // +1 so it fits with the previous output
        // TODO add bw simplification record
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
bool BackwardSubsumptionDemodulation::simplifyCandidate2(Clause* sideCl, Clause* mainCl, MLMatcher2 const& matcher, Clause*& replacement)
{
  Ordering const& ordering = _salg->getOrdering();

  Literal* eqLit = matcher.getEqualityForDemodulation();
  if (!eqLit) {
    // eqLit == nullptr means that the whole side premise can be instantiated to some subset of the candidate,
    // i.e., we have subsumption.
#if VDEBUG && BSD_VDEBUG_REDUNDANCY_ASSERTIONS
    OverlayBinder tmpBinder;
    matcher.getBindings(tmpBinder.base());
    ASS(SDHelper::substClauseIsSmallerOrEqual(sideCl, tmpBinder, mainCl, ordering));
#endif
    ASS(replacement == nullptr);
    env.statistics->backwardSubsumed++;
    return true;
  }
  ASS(eqLit->isEquality());
  ASS(eqLit->isPositive());

  unsigned const eqSort = SortHelper::getEqualityArgumentSort(eqLit);

  Ordering::Result const eqArgOrder = ordering.getEqualityArgumentOrder(eqLit);
  bool const preordered = (eqArgOrder == Ordering::LESS) || (eqArgOrder == Ordering::GREATER);
  if (_preorderedOnly && !preordered) {
    return false;
  }

  // isMatched[i] is true iff (*mainCl)[i] is matched by some literal in sideCl (other than eqLit)
  static v_vector<bool> isMatched;
  matcher.getMatchedAltsBitmap(isMatched);

  static OverlayBinder binder;
  binder.clear();
  matcher.getBindings(binder.base());

  // NOTE: for explanation see comments in ForwardSubsumptionDemodulation2::perform
  static v_vector<TermList> lhsVector;
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

    NonVariableIterator nvi(dlit);
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

      if (SortHelper::getTermSort(lhsS, dlit) != eqSort) {
        continue;
      }

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

        // NOTE: see comments in ForwardSubsumptionDemodulation2::perform for explanation
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
              ASS(SDHelper::substClauseIsSmallerOrEqual(sideCl, binder, mainCl, ordering));
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
              // Note that mclθ < cl does not always hold here,
              // but we don't need it to ensure redundancy of cl
              // because cl is already entailed by replacement alone
              ASS(SDHelper::clauseIsSmaller(replacement, mainCl, ordering));
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
          Literal* eqLitS = Literal::createEquality(true, lhsS, rhsS, eqSort);
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

        Inference* inference = new Inference2(Inference::BACKWARD_SUBSUMPTION_DEMODULATION, mainCl, sideCl);
        Unit::InputType inputType = std::max(mainCl->inputType(), sideCl->inputType());

        Clause* newCl = new(mainCl->length()) Clause(mainCl->length(), inputType, inference);

        for (unsigned i = 0; i < mainCl->length(); ++i) {
          if (i == dli) {
            (*newCl)[i] = newLit;
          } else {
            (*newCl)[i] = (*mainCl)[i];
          }
        }

        newCl->setAge(mainCl->age());
        env.statistics->backwardSubsumptionDemodulations++;

        replacement = newCl;

#if BSD_LOG_INFERENCES
        env.beginOutput();
        env.out() << "\% Begin Inference \"BSD-" << newCl->number() << "\"\n";
        env.out() << "\% eqLit: " << eqLit->toString() << "\n";
        env.out() << "\% eqLitS: " << binder.applyTo(eqLit)->toString() << "\n";
        env.out() << "\% dlit: " << dlit->toString() << "\n";
        env.out() << "\% numMatches+1: success at match #" << (numMatches+1) << "\n";
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
}  // simplifyCandidate2


}
