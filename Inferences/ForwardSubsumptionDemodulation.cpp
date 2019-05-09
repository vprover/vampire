#include "ForwardSubsumptionDemodulation.hpp"

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

  _preorderedOnly = false;  // TODO: might add an option for this like in forward demodulation
  _performRedundancyCheck = getOptions().demodulationRedundancyCheck();
}

void ForwardSubsumptionDemodulation::detach()
{
  CALL("ForwardSubsumptionDemodulation::detach");
  _index.release();
  ForwardSimplificationEngine::detach();
}


/**
 * A binder that consists of two maps, a base and an overlay.
 * Lookup first checks the base map, then the overlay map.
 * New bindings are added to the overlay map.
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
    BindingsMap& base()
    {
      ASS(m_overlay.empty());
      return m_base;
    }

    /// Resets to base bindings
    void reset() {
      m_overlay.clear();
    }

    // /// Resets to the given base bindings
    // void resetToBase(BindingsMap&& newBase)
    // {
    //   m_base = std::move(newBase);
    //   m_overlay.clear();
    // }

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
          // If var is not bound, return the variable itself (as TermList)
          return TermList(var, false);
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
};


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
  // whenever lΘ > rΘ
  // and   l = r \/ C   <   CΘ \/ L[lΘ] \/ D    (s.t. the right premise is redundant after the inference)

  TimeCounter tc(TC_FORWARD_SUBSUMPTION_DEMODULATION);

  Ordering& ordering = _salg->getOrdering();

  // Discards all previous aux values (so after this, hasAux() returns false for any clause).
  Clause::requestAux();
  ON_SCOPE_EXIT( Clause::releaseAux(); );

  // Initialize miniIndex with literals in the clause cl
  LiteralMiniIndex miniIndex(cl);

  for (unsigned sqli = 0; sqli < cl->length(); ++sqli) {
    Literal* subsQueryLit = (*cl)[sqli];  // this literal is only used to query the subsumption index

#if CHECK_FOR_MULTIPLE_RESULTS
    int fsd_result_count = 0;
    Clause* fsd_first_mcl = nullptr;
    Clause* fsd_first_result = nullptr;
    v_set<v_set<Literal*>> fsd_results;
#endif

    SLQueryResultIterator rit = _index->getGeneralizations(subsQueryLit, false, false);
    while (rit.hasNext()) {
      SLQueryResult res = rit.next();
      Clause* mcl = res.clause;

      ASS_NEQ(cl, mcl);  // this can't happen because cl isn't in the index yet

      if (mcl->hasAux()) {
        // we've already checked this clause
        continue;
      }
      mcl->setAux(nullptr);

      if (!ColorHelper::compatible(cl->color(), mcl->color())) {
        continue;
      }

      // No multiset match possible if base is longer than instance
      if (mcl->length() > cl->length()) {
        continue;
      }

      // Find a positive equality in mcl to use for demodulation
      for (unsigned eqi = 0; eqi < mcl->length(); ++eqi) {
        Literal* eqLit = (*mcl)[eqi];  // Equality literal for demodulation
        if (!eqLit->isEquality()) {
          continue;
        }
        if (eqLit->isNegative()) {
          continue;
        }
        ASS(eqLit->isEquality());
        ASS(eqLit->isPositive());

        unsigned const eqSort = SortHelper::getEqualityArgumentSort(eqLit);

        Ordering::Result argOrder = ordering.getEqualityArgumentOrder(eqLit);
        bool preordered = (argOrder == Ordering::LESS) || (argOrder == Ordering::GREATER);
        if (_preorderedOnly && !preordered) {
          continue;
        }

        // Now we have to check if (mcl without eqLit) can be instantiated to some subset of cl
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

            // TODO: order alternatives, either smaller to larger or larger to smaller, or unordered
            // to do this, can we simply order the literals inside the miniIndex? (in each equivalence class w.r.t. literal header)
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

          static v_unordered_set<Literal*> matchedAlts(16);
          matchedAlts.clear();
          matcher.getMatchedAlts(matchedAlts);

          static OverlayBinder binder;
          binder.clear();
          matcher.getBindings(binder.base());

          // Now we try to demodulate some term in an unmatched literal with eqLit.
          // IMPORTANT: only look at literals that are not being matched to mcl (the rule is unsound otherwise)!
          //
          //     mcl                cl
          // vvvvvvvvvv      vvvvvvvvvvvvvvvv
          // eqLit         matched      /-- only look for a term to demodulate in this part!
          // vvvvv           vv    vvvvvvvvvv
          // l = r \/ C      CΘ \/ L[lΘ] \/ D
          // --------------------------------
          //       CΘ \/ L[rΘ] \/ D

          bool postMLMatchOrdered = preordered;
          if (!preordered) {
            Literal* eqLitS = binder.applyTo(eqLit);
            auto argOrder = ordering.getEqualityArgumentOrder(eqLitS);
            postMLMatchOrdered = (argOrder == Ordering::LESS) || (argOrder == Ordering::GREATER);
          }

          // TODO: inline getDemodulationLHSIterator (it uses options for FwDem that don't apply here; and does checks that aren't necessary here)
          auto lhsIt = EqHelper::getDemodulationLHSIterator(eqLit, true, ordering, getOptions());
          while (lhsIt.hasNext()) {
            TermList lhs = lhsIt.next();
            TermList rhs = EqHelper::getOtherEqualitySide(eqLit, lhs);

#if VDEBUG
            if (preordered) {
              if (argOrder == Ordering::LESS) {
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
              if (matchedAlts.find(dlit) != matchedAlts.end()) {
                continue;
              }

              // TODO: discuss
              if (dlit == eqLit) {
                // Only possible match would lead to an equality tautology => skip this literal
                // static int eqcnt = 0;
                // ++eqcnt;
                // std::cerr << "eqcnt = " << eqcnt << std::endl;
                // continue;

                // Actually:
                // Whenever it is possible to derive an equality tautology,
                // we should do it because it allows us to delete a clause
                // TODO: redundancy should be fine here. in the worst case the clauses are equal, but then we can delete this one anyways.
                env.statistics->forwardSubsumptionDemodulationsToEqTaut++;
                premises = pvi(getSingletonIterator(mcl));
                replacement = nullptr;
                return true;
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
                if (MatchingUtils::matchTerms(lhs, lhsS, binder)) {
                  TermList rhsS = binder.applyTo(rhs);
                  ASS_EQ(lhsS, binder.applyTo(lhs));

                  if (!postMLMatchOrdered && ordering.compare(lhsS, rhsS) != Ordering::GREATER) {
                    continue;
                  }

                  bool performToplevelCheck = _performRedundancyCheck && dlit->isEquality() && (lhsS == *dlit->nthArgument(0) || lhsS == *dlit->nthArgument(1));
                  if (performToplevelCheck) {
                    //   lhsS=rhsS
                    //    eqLitS          dlit
                    //    vvvvv          vvvvv
                    //    l = r \/ C     l = t \/ D
                    //   ---------------------------
                    //        r = t \/ D
                    TermList other = EqHelper::getOtherEqualitySide(dlit, lhsS);   // t
                    Ordering::Result tord = ordering.compare(rhsS, other);
                    if (tord != Ordering::LESS && tord != Ordering::LESS_EQ) {  // TODO: why is LESS_EQ ok?   tord == LESS_EQ  ==>  r ≤ t  ==>  l=r ≤ l=t  ==>  ??? (Don't we need strictly less here?)
                      Literal* eqLitS = binder.applyTo(eqLit);
                      // TODO: check this again with the writeup of FSD
                      bool isMax = true;
                      for (unsigned li2 = 0; li2 < cl->length(); li2++) {
                        if (dli == li2) {
                          continue;
                        }
                        Literal* lit2 = (*cl)[li2];
                        if (ordering.compare(eqLitS, (*cl)[li2]) == Ordering::LESS) {
                          isMax = false;
                          break;
                        }
                      }
                      if (isMax) {
                        // std::cerr << "toplevel check prevented something" << std::endl;
                        // We have the following case which doesn't preserve completeness:
                        //    l = r \/ C     l = t \/ D
                        //   ---------------------------
                        //        r = t \/ D
                        // where r > t and l = r > D.
                        //
                        // Reason:
                        // the right premise should become redundant after application of FSD (since it is a simplification rule).
                        // It is redundant, if it is a logical consequence of smaller clauses in the search space.
                        // * It is easy to see that the right premise is a logical consequence of the conclusion and the left premise.
                        // * Also, the right premise is larger than the conclusion, because l > r.
                        // * However, we also need that the left premise is smaller than the right premise.
                        //   Three cases for dlit (the literal in the right premise to be demodulated):
                        //   1. L[l] in the right premise is not an equality literal. Then L[l] > l = r because equalities are smallest in the ordering.
                        //   2. s[l] = t with s[l] ≠ l. Then s[l] > l (subterm property of simplification orderings).
                        //                              Thus s[l] = t > l = r.  (multiset extension of ordering: { s[l], t } > { s[l] } > { l, r }, because s[l] > l > r)
                        //   3. l = t in the right premise.
                        //   3a. If r ≤ t, then l = r ≤ l = t.
                        //   3b. Otherwise we have to perform the toplevel check. isMax iff l = r > D.
                        //
                        //   Now we have a literal L in the right premise such that L > l = r.
                        //   We know that Cσ is a sub-multiset of D, thus C ≤ Cσ ≤ D.
                        //
                        //   What if
                        //   l = r \/ L \/ P  ;  l = t \/ L \/ P \/ Q   and r > t ???
                        continue;
                      }
                    }
                  }  // if (performToplevelCheck)

                  Literal* newLit = EqHelper::replace(dlit, lhsS, rhsS);
                  ASS_EQ(ordering.compare(lhsS, rhsS), Ordering::GREATER);
                  ASS_EQ(ordering.compare(dlit, newLit), Ordering::GREATER);

                  if (EqHelper::isEqTautology(newLit)) {
                    env.statistics->forwardSubsumptionDemodulationsToEqTaut++;

                    // TODO: discuss this;
                    // we might find another useful match after encountering an equality tautology,
                    // so maybe we should continue here.
                    // (After the other optimizations, this is no issue anymore for our oxford-fsd example.
                    //  "FSD after FS" eliminated most of the equality tautologies.;
                    //  the "dlit == eqLit" check eliminated the rest.)
                    // NOTE:
                    // Actually, when we get an equality tautology, it means the given clause can be deleted.
                    // So it's actually good if we end up in this case.

                    premises = pvi(getSingletonIterator(mcl));
                    replacement = nullptr;
                    // Clause reduction was successful (=> return true),
                    // but we don't set the replacement (because the result is a tautology and should be discarded)
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

                  // TODO:
                  // If we continue here, we find a lot more inferences (but takes a long time; factor 2);
                  // continue;

                  // Return early to measure the impact of computation without affecting the search space
                  // return false;

                  premises = pvi(getSingletonIterator(mcl));
                  replacement = newCl;
                  // std::cerr << "\t FwSubsDem replacement: " << replacement->toNiceString() << std::endl;
                  // std::cerr << "\t          for input cl: " << cl->toNiceString() << std::endl;
                  // std::cerr << "\t               via mcl: " << mcl->toNiceString() << std::endl;
                  return true;
                } // if (lhs matches lhsS)
              } // while (nvi.hasNext())
            } // for dli
          } // while (lhsIt.hasNext())
        } // for (numMatches)
      } // for eqi
    } // while (rit.hasNext)
  } // for (li)

  return false;
}
