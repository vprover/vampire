#include "ForwardSubsumptionDemodulation.hpp"

#include "Debug/RuntimeStatistics.hpp"
#include "Indexing/Index.hpp"
#include "Indexing/IndexManager.hpp"
#include "Indexing/LiteralIndex.hpp"
#include "Indexing/LiteralMiniIndex.hpp"
#include "Kernel/ColorHelper.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/MLMatcher.hpp"
#include "Kernel/Matcher.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Sorts.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Term.hpp"
#include "Lib/ScopeGuard.hpp"
#include "Lib/STL.hpp"
#include "Lib/STLAllocator.hpp"
#include "Saturation/SaturationAlgorithm.hpp"
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

  auto index_type = getOptions().forwardSubsumptionDemodulationUseSeparateIndex() ? FSD_SUBST_TREE : FW_SUBSUMPTION_SUBST_TREE;
  _index.request(salg->getIndexManager(), index_type);

  _preorderedOnly = false;
  _allowIncompleteness = false;
}


void ForwardSubsumptionDemodulation::detach()
{
  CALL("ForwardSubsumptionDemodulation::detach");
  _index.release();
  ForwardSimplificationEngine::detach();
}


namespace {


/**
 * A binder that consists of two maps: a base and an overlay.
 * Lookup first checks the base map, then the overlay map.
 * New bindings are added to the overlay map.
 *
 * In FSD, the base bindings are extracted from the MLMatcher and correspond to the subsumption part,
 * while the overlay bindings are from the demodulation part (i.e., from
 * matching the lhs of the demodulation equality to the candidate term that
 * might be simplified).
 *
 * This class implements the Binder interface as described in Kernel/Matcher.hpp,
 * and the Applicator interface as described in Kernel/SubstHelper.hpp.
 */
class OverlayBinder
{
  public:
    using Var = unsigned int;
    using BindingsMap = v_unordered_map<Var, TermList>;

    OverlayBinder()
      : m_base(16)
      , m_overlay(16)
    { }

    /// Initializes the base bindings with the given argument
    explicit
    OverlayBinder(BindingsMap&& initialBindings)
      : m_base(std::move(initialBindings))
      , m_overlay(16)
    { }

    bool bind(Var var, TermList term)
    {
      // If the variable is already bound, it must be bound to the same term.
      auto base_it = m_base.find(var);
      if (base_it != m_base.end()) {
        return base_it->second == term;
      }
      else {
        auto res = m_overlay.insert({var, term});
        auto it = res.first;
        bool inserted = res.second;
        return inserted || (it->second == term);
      }
    }

    bool isBound(Var var)
    {
      return m_base.find(var) != m_base.end()
        || m_overlay.find(var) != m_overlay.end();
    }

    void specVar(Var var, TermList term)
    {
      ASSERTION_VIOLATION;
    }

    /// Clear all bindings
    void clear()
    {
      m_base.clear();
      m_overlay.clear();
    }

    /// Direct access to base bindings.
    /// The returned map may only be modified if the overlay map is empty!
    /// (this function is unfortunately necessary to be able to extract the base bindings from the MLMatcher without dynamic memory allocation)
    BindingsMap& base()
    {
      ASS(m_overlay.empty());
      return m_base;
    }

    /// Resets to base bindings
    void reset() {
      m_overlay.clear();
    }

    // Makes objects of this class work as applicator for substitution
    // (as defined in Kernel/SubstHelper.hpp)
    TermList apply(Var var) const {
      auto b_it = m_base.find(var);
      if (b_it != m_base.end()) {
        return b_it->second;
      } else {
        auto o_it = m_overlay.find(var);
        if (o_it != m_overlay.end()) {
          return o_it->second;
        } else {
          // We should never access unbound variables
          // (NOTE: we should not return the variable itself here, as this creates a risk of mixing variables coming from different clauses)
          ASSERTION_VIOLATION;
        }
      }
    }

    TermList applyTo(TermList t, bool noSharing = false) const {
      return SubstHelper::apply(t, *this, noSharing);
    }

    Literal* applyTo(Literal* l) const {
      return SubstHelper::apply(l, *this);
    }

  private:
    BindingsMap m_base;
    BindingsMap m_overlay;
};  // class OverlayBinder


/**
 * Build clause that results from subsumption resolution with main premise 'cl' and side premise 'mcl'.
 * The literal 'resLit' is the resolved literal from 'cl'.
 */
Clause* generateSubsumptionResolutionClause(Clause* cl, Literal* resLit, Clause* mcl)
{
  CALL("generateSubsumptionResolutionClause");

  Inference* inference = new Inference2(Inference::SUBSUMPTION_RESOLUTION, cl, mcl);
  Unit::InputType inputType = std::max(cl->inputType(), mcl->inputType());

  unsigned newLen = cl->length() - 1;
  Clause* newCl = new(newLen) Clause(newLen, inputType, inference);

  unsigned j = 0;
  for (unsigned i = 0; i < cl->length(); ++i) {
    Literal* curLit = (*cl)[i];

    if (curLit != resLit) {
      (*newCl)[j] = curLit;
      j += 1;
    }
  }
  // We should have skipped exactly one literal, namely resLit.
  // (it should never appear twice because we apply duplicate literal removal before subsumption resolution)
  ASS_EQ(j, newLen);

  newCl->setAge(cl->age());

  return newCl;
}


}  // namespace


#define CHECK_FOR_MULTIPLE_RESULTS 0

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
  ON_SCOPE_EXIT( Clause::releaseAux(); );

  // Initialize miniIndex with literals in the clause cl
  LiteralMiniIndex const miniIndex(cl);

  for (unsigned sqli = 0; sqli < cl->length(); ++sqli) {
    Literal* subsQueryLit = (*cl)[sqli];  // this literal is only used to query the subsumption index

#if CHECK_FOR_MULTIPLE_RESULTS
    int fsd_result_count = 0;
    Clause* fsd_first_mcl = nullptr;
    Clause* fsd_first_result = nullptr;
    v_set<v_set<Literal*>> fsd_results;
#endif

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
       * Step 2: choose a positive equality in mcl to use for demodulation
       */
      for (unsigned eqi = 0; eqi < mcl->length(); ++eqi) {
        Literal* eqLit = (*mcl)[eqi];  // Equality literal for demodulation
        if (!eqLit->isEquality() || !eqLit->isPositive()) {
          continue;
        }

        unsigned const eqSort = SortHelper::getEqualityArgumentSort(eqLit);

        Ordering::Result const eqArgOrder = ordering.getEqualityArgumentOrder(eqLit);
        bool const preordered = (eqArgOrder == Ordering::LESS) || (eqArgOrder == Ordering::GREATER);
        if (_preorderedOnly && !preordered) {
          continue;
        }

        /**
         * Step 3: check if mcl (without eqLit) can be instantiated to some subset of cl
         */
        static v_vector<Literal*> baseLits;
        static v_vector<LiteralList*> alts;
        baseLits.clear();
        alts.clear();
        baseLits.reserve(mcl->length() - 1);
        alts.reserve(mcl->length() - 1);
        ASS_EQ(baseLits.size(), 0);
        ASS_EQ(alts.size(), 0);
        for (unsigned mi = 0; mi < mcl->length(); ++mi) {
          if (mi != eqi) {
            Literal* base = (*mcl)[mi];
            baseLits.push_back(base);

            LiteralList* l = nullptr;

            LiteralMiniIndex::InstanceIterator instIt(miniIndex, base, false);
            while (instIt.hasNext()) {
              Literal* matched = instIt.next();
              LiteralList::push(matched, l);
            }

            alts.push_back(l);
          }
        }
        ASS_GE(baseLits.size(), 1);
        ASS_EQ(baseLits.size(), alts.size());

        // Ensure cleanup of LiteralLists
        ON_SCOPE_EXIT({
          for (LiteralList* ll : alts) {
            LiteralList::destroy(ll);
          }
        });

        static MLMatcher matcher;
        matcher.init(baseLits.data(), baseLits.size(), cl, alts.data(), true);

        static unsigned const maxMatches =
          getOptions().forwardSubsumptionDemodulationMaxMatches() == 0
          ? std::numeric_limits<decltype(maxMatches)>::max()
          : getOptions().forwardSubsumptionDemodulationMaxMatches();

        for (unsigned numMatches = 0; numMatches < maxMatches; ++numMatches) {
          if (!matcher.nextMatch()) {
            break;
          }

          // isMatched[i] is true iff (*cl)[i] is matched my some literal in mcl (without eqLit)
          static v_vector<bool> isMatched;
          matcher.getMatchedAltsBitmap(isMatched);

          static OverlayBinder binder;
          binder.clear();
          matcher.getBindings(binder.base());

          /**
           * Step 4: now we try to demodulate some term in an unmatched literal with eqLit.
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

          static v_vector<TermList> lhsVector;
          lhsVector.clear();
          {
            TermList t0 = *eqLit->nthArgument(0);
            TermList t1 = *eqLit->nthArgument(1);
            switch (eqArgOrder) {
              case Ordering::INCOMPARABLE:
                ASS(!_preorderedOnly);  // would've skipped earlier already
                // NOTE: We cannot exclude an LHS here by checking t0.containsAllVariablesOf(t1) etc., because
                // this property might change after substitution (note that unlike demodulation, the substitution here
                // does not only come from the equality, but also from the subsumption part).
                lhsVector.push_back(t0);
                lhsVector.push_back(t1);
                break;
              case Ordering::GREATER:
              case Ordering::GREATER_EQ:
                ASS(t0.containsAllVariableOccurrencesOf(t1));
                ASS(t0.containsAllVariablesOf(t1));
                lhsVector.push_back(t0);
                break;
              case Ordering::LESS:
              case Ordering::LESS_EQ:
                ASS(t1.containsAllVariableOccurrencesOf(t0));
                ASS(t1.containsAllVariablesOf(t0));
                lhsVector.push_back(t1);
                break;
              case Ordering::EQUAL:
                // there should be no equality literals with equal terms
                ASSERTION_VIOLATION;
              default:
                ASSERTION_VIOLATION;
            }
          }

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

            static DHSet<TermList> attempted;  // Terms we already attempted to demodulate
            attempted.reset();

            for (unsigned dli = 0; dli < cl->length(); ++dli) {
              Literal* dlit = (*cl)[dli];  // literal to be demodulated

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

                binder.reset();  // reset binder to state after subsumption check
                if (!MatchingUtils::matchTerms(lhs, lhsS, binder)) {
                  continue;
                }

                // NOTE: If at this point there is a variable in mcl that is not
                // yet bound in binder, then this variable occurs only in rhs.
                // The reason is that all other literals have been matched by the
                // MLMatcher, and lhs has been matched to lhsS just now.
                //
                // In order to keep the variables of the two premises separate,
                // we must map any of these yet-unbound variables to some other
                // variables that do not occur in the main premise cl.
                //
                // Furthermore, if there is a variable that occurs only in rhsS,
                // then lhsS and rhsS will always be INCOMPARABLE in the term
                // ordering, so we cannot apply FSD in this case.
                {
                  bool hasUnboundVar = false;
                  VariableIterator rhsVarIt(rhs);
                  while (rhsVarIt.hasNext()) {
                    TermList rhsVar = rhsVarIt.next();
                    if (!binder.isBound(rhsVar.var())) {
                      hasUnboundVar = true;
                      break;
                    }
                  }
                  if (hasUnboundVar) {
                    // lhsS and rhsS are INCOMPARABLE because there is a variable that only occurs in rhsS
                    RSTAT_CTR_INC("FSDv1, match rejected due to unbound variables in rhs");
                    continue;
                  }
                }

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
                      ASS_EQ(binder.applyTo(eqLit), dlit);  // eqLitS == dlit
                      ASS(!getOptions().forwardSubsumption());
                      premises = pvi(getSingletonIterator(mcl));
                      env.statistics->forwardSubsumed++;
                      return true;
                    } else {
                      // Here, we have subsumption resolution
                      ASS_EQ(binder.applyTo(eqLit), Literal::complementaryLiteral(dlit));  // ¬eqLitS == dlit
                      ASS_EQ(ordering.compare(binder.applyTo(eqLit), dlit), Ordering::GREATER);  // L > ¬L
                      ASS(!getOptions().forwardSubsumptionResolution());
                      // TODO: ASS(checkForSubsumptionResolution(cl, cm, dlit));
                      replacement = generateSubsumptionResolutionClause(cl, dlit, mcl);
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
                  Literal* eqLitS = Literal::createEquality(true, lhsS, rhsS, eqSort);
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
                  RSTAT_CTR_INC("FSDv1, main premise not redundant");
                  continue;
                }  // if (!_allowIncompleteness)
isRedundant:

                /**
                 * Step 5: found application of FSD; now create the conclusion
                 */
                Literal* newLit = EqHelper::replace(dlit, lhsS, rhsS);
                ASS_EQ(ordering.compare(lhsS, rhsS), Ordering::GREATER);
                ASS_EQ(ordering.compare(dlit, newLit), Ordering::GREATER);

                if (EqHelper::isEqTautology(newLit)) {
                  env.statistics->forwardSubsumptionDemodulationsToEqTaut++;
                  premises = pvi(getSingletonIterator(mcl));
                  replacement = nullptr;
                  return true;
                }

                Inference* inference = new Inference2(Inference::FORWARD_SUBSUMPTION_DEMODULATION, cl, mcl);
                Unit::InputType inputType = std::max(cl->inputType(), mcl->inputType());

                Clause* newCl = new(cl->length()) Clause(cl->length(), inputType, inference);

                for (unsigned i = 0; i < cl->length(); ++i) {
                  if (i == dli) {
                    (*newCl)[i] = newLit;
                  } else {
                    (*newCl)[i] = (*cl)[i];
                  }
                }

                newCl->setAge(cl->age());
                env.statistics->forwardSubsumptionDemodulations++;

#if CHECK_FOR_MULTIPLE_RESULTS
                v_set<Literal*> newClSet;
                for (unsigned i = 0; i < newCl->length(); ++i) {
                  newClSet.insert((*newCl)[i]);
                }
                auto ins_res = fsd_results.insert(newClSet);
                bool result_is_new = ins_res.second;
                fsd_result_count += 1;
                if (fsd_result_count == 1) {
                  ASS(!fsd_first_mcl);
                  ASS(!fsd_first_result);
                  fsd_first_mcl = mcl;
                  fsd_first_result = newCl;
                }
                if (fsd_result_count >= 2 && result_is_new) {
                  if (fsd_result_count == 2) {
                    std::cerr << "\n\n";
                    std::cerr << "fsd_count = 1" << std::endl;
                    std::cerr << "   mcl = " << fsd_first_mcl->toNiceString() << std::endl;
                    std::cerr << "   cl  = " << cl->toNiceString() << std::endl;
                    std::cerr << "   res = " << fsd_first_result->toNiceString() << std::endl;
                  }
                  std::cerr << "fsd_count = " << fsd_result_count << std::endl;
                  std::cerr << "   mcl = " << mcl->toNiceString() << std::endl;
                  std::cerr << "   cl  = " << cl->toNiceString() << std::endl;
                  std::cerr << "   res = " << newCl->toNiceString() << std::endl;
                }
#endif

                premises = pvi(getSingletonIterator(mcl));
                replacement = newCl;
                return true;
              }  // while (nvi.hasNext())
            }  // for (dli)
          }  // for (lhs)
        }  // for (numMatches)
      }  // for (eqi)
    }  // while (rit.hasNext)
  }  // for (li)

  return false;
}
