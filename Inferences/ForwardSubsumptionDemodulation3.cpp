#include "ForwardSubsumptionDemodulation3.hpp"

#include "Debug/RuntimeStatistics.hpp"
#include "Indexing/Index.hpp"
#include "Indexing/IndexManager.hpp"
#include "Indexing/LiteralIndex.hpp"
#include "Indexing/LiteralMiniIndex.hpp"
#include "Kernel/ColorHelper.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/MLMatcher.hpp"
#include "Kernel/MLMatcher2.hpp"
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
#include "Shell/TPTPPrinter.hpp"
#include <array>
#include <unordered_map>
#include <unordered_set>
#include <vector>

using namespace Kernel;
using namespace Lib;
using namespace Inferences;
using namespace Saturation;


// Set to true to output FSD inferences on stdout
#define FSD_LOG_INFERENCES false

// Set to true to check redundancy of simplified clause in debug mode
#define FSD_VDEBUG_REDUNDANCY_ASSERTIONS true


void ForwardSubsumptionDemodulation3::attach(SaturationAlgorithm* salg)
{
  CALL("ForwardSubsumptionDemodulation3::attach");
  ForwardSimplificationEngine::attach(salg);

  auto index_type = getOptions().forwardSubsumptionDemodulationUseSeparateIndex() ? FSD_SUBST_TREE : FW_SUBSUMPTION_SUBST_TREE;
  _index.request(salg->getIndexManager(), index_type);

  _preorderedOnly = false;
  _allowIncompleteness = false;

  if (_doSubsumption) {
    _unitIndex.request(salg->getIndexManager(), SIMPLIFYING_UNIT_CLAUSE_SUBST_TREE);
  }

  if (_doSubsumptionResolution && !_doSubsumption) {
    USER_ERROR("FSDv3: forward subsumption resolution requires forward subsumption to be enabled.");
  }
}


void ForwardSubsumptionDemodulation3::detach()
{
  CALL("ForwardSubsumptionDemodulation3::detach");
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
    void reset()
    {
      m_overlay.clear();
    }

    bool tryGetBinding(Var var, TermList& result) const
    {
      auto b_it = m_base.find(var);
      if (b_it != m_base.end()) {
        // var has base binding
        result = b_it->second;
        return true;
      } else {
        auto o_it = m_overlay.find(var);
        if (o_it != m_overlay.end()) {
          // var has overlay binding
          result = o_it->second;
          return true;
        } else {
          // var is unbound
          return false;
        }
      }
    }

    /// Makes objects of this class work as applicator for substitution
    /// (as defined in Kernel/SubstHelper.hpp)
    TermList apply(Var var) const
    {
      TermList result;
      if (tryGetBinding(var, result)) {
        return result;
      } else {
        // We should never access unbound variables
        // (NOTE: we should not return the variable itself here, as this creates a risk of mixing variables coming from different clauses)
        ASSERTION_VIOLATION;
      }
    }

    TermList applyTo(TermList t, bool noSharing = false) const
    {
      return SubstHelper::apply(t, *this, noSharing);
    }

    Literal* applyTo(Literal* l) const
    {
      return SubstHelper::apply(l, *this);
    }

    /// Like applyTo, but all unbound variables are shifted by unboundVarOffset
    TermList applyWithUnboundVariableOffsetTo(TermList t, Var unboundVarOffset, bool noSharing = false) const
    {
      WithUnboundVariableOffsetApplicator applicator(*this, unboundVarOffset);
      return SubstHelper::apply(t, applicator, noSharing);
    }

  private:
    class WithUnboundVariableOffsetApplicator
    {
      public:
        WithUnboundVariableOffsetApplicator(OverlayBinder const& binder, Var unboundVarOffset)
          : binder(binder), unboundVarOffset(unboundVarOffset)
        { }

        /// Does the same as OverlayBinder::apply, except for the case where the variable is not bound
        TermList apply(Var var) const
        {
          TermList result;
          if (binder.tryGetBinding(var, result)) {
            return result;
          } else {
            // No bindings? return the variable shifted by offset
            return TermList(var + unboundVarOffset, false);
          }
        }

      private:
        OverlayBinder const& binder;
        Var unboundVarOffset;
    };

  private:
    BindingsMap m_base;
    BindingsMap m_overlay;

    friend std::ostream& operator<<(std::ostream& o, OverlayBinder const& binder);
};  // class OverlayBinder

std::ostream& operator<<(std::ostream& o, OverlayBinder const& binder)
{
  o << "OverlayBinder { ";
  bool first = true;
  for (auto binding : binder.m_base) {
    if (!first) {
      o << ", ";
    } else {
      first = false;
    }
    o << TermList(binding.first, false).toString() << " -> " << binding.second.toString();
  }
  o << " / ";
  first = true;
  for (auto binding : binder.m_overlay) {
    if (!first) {
      o << ", ";
    } else {
      first = false;
    }
    o << TermList(binding.first, false).toString() << " -> " << binding.second.toString();
  }
  o << " }";
  return o;
}


#if VDEBUG
/// Returns true iff clause with literal lits1 is smaller than clause with literals lits2
/// in the multiset extension of the given ordering.
///
/// This implementation is justified by Lemma 2.5.6 on page 24 of [BN98].
/// [BN98] Franz Baader and Tobias Nipkow. Term Rewriting and All That. Cambridge University Press, 1998.
bool clauseIsSmaller(Literal* const lits1[], unsigned n1, Literal* const lits2[], unsigned n2, Ordering const& ordering)
{
  // Copy given literals so we can sort them
  v_vector<Literal*> c1(lits1, lits1+n1);
  v_vector<Literal*> c2(lits2, lits2+n2);

  // These will contain literals from c1/c2 with equal occurrences removed
  v_vector<Literal*> v1;
  v_vector<Literal*> v2;

  // Sort input by pointer value
  // NOTE: we use std::less<> because the C++ standard guarantees it is a total order on pointer types.
  //       (the built-in operator< is not required to be a total order for pointer types.)
  std::less<Literal*> const lit_ptr_less;
  std::sort(c1.begin(), c1.end(), lit_ptr_less);
  std::sort(c2.begin(), c2.end(), lit_ptr_less);

  // Skip occurrences of equal literals
  unsigned i1 = 0;
  unsigned i2 = 0;
  while (i1 < n1 && i2 < n2) {
    if (c1[i1] == c2[i2]) {
      // skip this occurrence
      ++i1;
      ++i2;
    }
    else if (lit_ptr_less(c1[i1], c2[i2])) {
      v1.push_back(c1[i1]);
      ++i1;
    }
    else if (lit_ptr_less(c2[i2], c1[i1])) {
      v2.push_back(c2[i2]);
      ++i2;
    }
    else {
      ASSERTION_VIOLATION;
    }
  }
  while (i1 < n1) {
    ASS_GE(i2, n2);
    v1.push_back(c1[i1]);
    ++i1;
  }
  while (i2 < n2) {
    ASS_GE(i1, n1);
    v2.push_back(c2[i2]);
    ++i2;
  }

  if (v1.empty() && v2.empty()) {
    // Both clauses are the same
    ASS(c1 == c2);
    return false;
  }

  // For each remaining literal from c1,
  // we have to find a greater one in the remaining ones from c2.
  for (Literal* l1 : v1) {
    bool isCovered = false;
    for (Literal* l2 : v2) {
      switch (ordering.compare(l1, l2)) {
        case Ordering::LESS:
          // yay
          isCovered = true;
          break;
        case Ordering::INCOMPARABLE:
        case Ordering::GREATER:
          // doesn't work
          break;
        case Ordering::EQUAL:
          // should not happen due to first part where we remove equal literals
          ASSERTION_VIOLATION;
        case Ordering::LESS_EQ:
        case Ordering::GREATER_EQ:
          // those don't appear
          ASSERTION_VIOLATION;
        default:
          ASSERTION_VIOLATION;
      }
      if (isCovered) {
        break;
      }
    }
    if (!isCovered) {
      return false;
    }
  }

  return true;
}
#endif  // VDEBUG


/**
 * Stores an instance of the multi-literal matching problem.
 * Allows us to re-use the alts from subsumption for subsumption resolution.
 */
class ClauseMatches
{
  public:
    ClauseMatches(Clause* base, LiteralMiniIndex const& ixAlts);

    ~ClauseMatches();

    // Disallow copy
    ClauseMatches(ClauseMatches const&) = delete;
    ClauseMatches& operator=(ClauseMatches const&) = delete;

    // Default move is fine
    ClauseMatches(ClauseMatches&&) = default;
    ClauseMatches& operator=(ClauseMatches&&) = default;

    Clause* base() const { return m_base; }
    LiteralList const* const* alts() const { return m_alts.data(); }

    unsigned baseLitsWithoutAlts() const { return m_baseLitsWithoutAlts; }

    bool isSubsumptionPossible() const
    {
      // For subsumption, every base literal must have at least one alternative
      return m_baseLitsWithoutAlts == 0;
    }

    bool isSubsumptionDemodulationPossible() const
    {
      ASS_GE(m_baseLitsWithoutAlts, m_basePosEqsWithoutAlts);
      // Demodulation needs at least one positive equality
      if (m_basePosEqs == 0) {
        return false;
      }
      // If there are base literals without any suitable alternatives:
      // 1. If there is only one literal without alternative and it is a positive equality,
      //    then it might still be possible to get an FSD inference by choosing this literal
      //    as equality for demodulation.
      // 2. If there is a literal without alternative but it is not a positive equality,
      //    then it is impossible to get an FSD inference.
      // 3. If there are two literals without alternatives, then it is impossible as well.
      return m_baseLitsWithoutAlts == 0  // every base literal has alternatives
        || (m_baseLitsWithoutAlts == 1 && m_basePosEqsWithoutAlts == 1);  // case 1 in comment above
    }

  private:
    Clause* m_base;
    v_vector<LiteralList*> m_alts;
    unsigned m_basePosEqs;
    unsigned m_baseLitsWithoutAlts;
    unsigned m_basePosEqsWithoutAlts;
};  // class ClauseMatches

ClauseMatches::ClauseMatches(Clause* base, LiteralMiniIndex const& ixAlts)
  : m_base(base)
  , m_alts(base->length(), LiteralList::empty())
  , m_basePosEqs(0)
  , m_baseLitsWithoutAlts(0)
  , m_basePosEqsWithoutAlts(0)
{
  for (unsigned i = 0; i < m_base->length(); ++i) {
    Literal* baseLit = (*m_base)[i];
    bool isPosEq = baseLit->isEquality() || baseLit->isPositive();

    if (isPosEq) {
      m_basePosEqs += 1;
    }

    LiteralMiniIndex::InstanceIterator instIt(ixAlts, baseLit, false);

    if (!instIt.hasNext()) {
      // baseLit does not have any suitable alternative at all!
      m_baseLitsWithoutAlts += 1;
      if (isPosEq) {
        m_basePosEqsWithoutAlts += 1;
      }
    }

    ASS(LiteralList::isEmpty(m_alts[i]));
    while (instIt.hasNext()) {
      Literal* matched = instIt.next();
      LiteralList::push(matched, m_alts[i]);
    }
  }
}

ClauseMatches::~ClauseMatches()
{
  for (LiteralList* ll : m_alts) {
    LiteralList::destroy(ll);
  }
}

bool checkForSubsumptionResolution(Clause* cl, ClauseMatches const& cm, Literal* resLit)
{
  Clause* mcl = cm.base();

  if (cm.baseLitsWithoutAlts() > 0) {
    // Got base literals without alts?
    // Then subsumption resolution is possible,
    // but only if we can resolve ALL of them away
    // (i.e., complementary-match with resLit)
    //
    // NOTE: if there is more than one base literal without alts,
    // subsumption resolution might still be possible
    // (if we can unify them and resolve them all away)
    for (unsigned i = 0; i < mcl->length(); ++i) {
      if (LiteralList::isEmpty(cm.alts()[i])) {
        if (!MatchingUtils::match((*mcl)[i], resLit, /* complementary = */ true)) {
          return false;
        }
      }
    }

  } else {
    // No base literal without alts?
    // Subsumption resolution is possible if at least one base lit can be resolved with resLit

    bool anyResolvable = false;
    for (unsigned i = 0; i < mcl->length(); ++i) {
      if (MatchingUtils::match((*mcl)[i], resLit, /* complementary = */ true)) {
        anyResolvable = true;
        break;
      }
    }
    if (!anyResolvable) {
      return false;
    }
  }

  // NOTE: we use MLMatcher here because we want *subset* inclusion (as opposed to submultiset)
  return MLMatcher::canBeMatched(mcl, cl, cm.alts(), resLit);
}


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


bool ForwardSubsumptionDemodulation3::perform(Clause* cl, Clause*& replacement, ClauseIterator& premises)
{
  CALL("ForwardSubsumptionDemodulation3::perform");

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
  }  // if (_doSubsumption)

  // Initialize miniIndex with literals in the clause cl
  // TODO(idea for later): maybe it helps to order alternatives, either smaller to larger or larger to smaller, or unordered
  // to do this, we can simply order the literals inside the miniIndex (i.e., in each equivalence class w.r.t. literal header)
  LiteralMiniIndex const cl_miniIndex(cl);

  unsigned int const cl_maxVar = cl->maxVar();


  static v_vector<ClauseMatches> altsStorage;
  ON_SCOPE_EXIT({ altsStorage.clear(); });
  ASS(altsStorage.empty());


  //////////////////////////////////////////////
  // Subsumption and Subsumption Demodulation //
  //////////////////////////////////////////////

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
      altsStorage.emplace_back(mcl, cl_miniIndex);
      ClauseMatches const& cm = altsStorage.back();
      ASS_EQ(cm.base(), mcl);  // make sure we got the right one (since C++17, emplace_back returns the new element)

      if (!_doSubsumption && !cm.isSubsumptionDemodulationPossible()) {
        // we don't do subsumption and no FSD is possible => skip (purely for performance reasons)
        RSTAT_CTR_INC("FSDv3, skipped side premise because no FSD possible");
        continue;
      }

      if (_doSubsumption && !cm.isSubsumptionPossible() && !cm.isSubsumptionDemodulationPossible()) {
        // we do subsumption but neither FS nor FSD is possible => skip (purely for performance reasons)
        RSTAT_CTR_INC("FSDv3, skipped side premise because neither FS nor FSD possible");
        continue;
      }

      static MLMatcher2 matcher;
      matcher.init(mcl, cl, cm.alts());

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
          premises = pvi(getSingletonIterator(mcl));
          env.statistics->forwardSubsumed++;
          return true;
        }
        ASS(eqLit->isEquality());
        ASS(eqLit->isPositive());

        unsigned const eqSort = SortHelper::getEqualityArgumentSort(eqLit);

        Ordering::Result const eqArgOrder = ordering.getEqualityArgumentOrder(eqLit);
        bool const preordered = (eqArgOrder == Ordering::LESS) || (eqArgOrder == Ordering::GREATER);
        if (_preorderedOnly && !preordered) {
          continue;
        }

        // isMatched[i] is true iff (*cl)[i] is matched my some literal in mcl (without eqLit)
        static v_vector<bool> isMatched;
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

        // TODO
        // now that we have the 'unbound variable offset' we could also do away with the OverlayBinder
        // and use two separate MapBinders instead.
        // is probably slightly faster.
        // Also, the new variables generated with 'unbound variable offset' are only temporary and will disappear in the final result.
        // so there is no blowup of variable indices.

        // Select candidate lhs of eqLit for demodulation.
        // Must be larger than the rhs after substitution.
        //
        // Three possible outcomes:
        // 1. No LHS (if INCOMPARABLE and different variables)
        // 2. One LHS
        // 3. Two LHSs (INCOMPARABLE and same variables)
        static v_vector<TermList> lhsVector;
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
          // Problem: might fill up term sharing structure due to the temporary terms.
          // Currently there is no way to compare terms under a substitution without materializing them,
          // and non-shared terms cannot be compared (triggers assertions in KBO at least).
          // TODO: to fix this, it would be nice to have a function such as
          //    Ordering::compare(TermList t1, std::function<TermList(unsigned)> theta1,
          //                      TermList t2, std::function<TermList(unsigned)> theta2)
          // which compares terms under the given substitution.
          // (if we're fine with moving the ordering implementation into headers,
          //  we can do this without code duplication and no performance penalty for the currently supported common case.)

          TermList t0S = binder.applyWithUnboundVariableOffsetTo(t0, cl_maxVar+1, false);
          TermList t1S = binder.applyWithUnboundVariableOffsetTo(t1, cl_maxVar+1, false);
          Ordering::Result eqArgOrderS = ordering.compare(t0S, t1S);
          if (eqArgOrder == Ordering::INCOMPARABLE && eqArgOrderS != Ordering::INCOMPARABLE) {
            RSTAT_CTR_INC("FSDv3, ordered after partial substitution");
          }
#else
          // No additional ordering check.
          // But note that we still need to substitute here to ensure correctness of the "containsAllVariables" check.
          // (Since we don't call Ordering::compare here, we do not need to insert the terms into the sharing structure.)
          // TODO: we could also implement a "containsAllVariables" relative to a substitution.
          TermList t0S = binder.applyWithUnboundVariableOffsetTo(t0, cl_maxVar+1, true);
          TermList t1S = binder.applyWithUnboundVariableOffsetTo(t1, cl_maxVar+1, true);
          ON_SCOPE_EXIT({
            if (t0S.isTerm()) {
              t0S.term()->destroyNonShared();
            }
            if (t1S.isTerm()) {
              t1S.term()->destroyNonShared();
            }
          });
          Ordering::Result eqArgOrderS = eqArgOrder;
#endif
          switch (eqArgOrderS) {
            case Ordering::INCOMPARABLE:
              ASS(!_preorderedOnly);  // would've skipped earlier already

              // If t0S does not contain all variable occurrences of t1S, then
              // t0Θ cannot be larger than t1Θ, where Θ is the final substitution.
              if (t0S.containsAllVariableOccurrencesOf(t1S)) {
                ASS(t0S.containsAllVariablesOf(t1S));
                lhsVector.push_back(t0);
              } else {
#if VDEBUG
                if (t0S.containsAllVariablesOf(t1S)) {
                  RSTAT_CTR_INC("FSDv3, skipped LHS due to multiset-contains-check of variables");
                }
#endif
              }
              if (t1S.containsAllVariableOccurrencesOf(t0S)) {
                ASS(t1S.containsAllVariablesOf(t0S));
                lhsVector.push_back(t1);
              } else {
#if VDEBUG
                if (t1S.containsAllVariablesOf(t0S)) {
                  RSTAT_CTR_INC("FSDv3, skipped LHS due to multiset-contains-check of variables");
                }
#endif
              }
              break;
            case Ordering::GREATER:
            case Ordering::GREATER_EQ:
              ASS(t0S.containsAllVariableOccurrencesOf(t1S));
              ASS(t0S.containsAllVariablesOf(t1S));
              lhsVector.push_back(t0);
              break;
            case Ordering::LESS:
            case Ordering::LESS_EQ:
              ASS(t1S.containsAllVariableOccurrencesOf(t0S));
              ASS(t1S.containsAllVariablesOf(t0S));
              lhsVector.push_back(t1);
              break;
            case Ordering::EQUAL:
              // This case may happen due to the partial substitution from the MLMatcher
              RSTAT_CTR_INC("FSDv3, terms equal after partial substitution");
              break;
            default:
              ASSERTION_VIOLATION;
          }
        }

        if (lhsVector.size() == 0) {
          RSTAT_CTR_INC("FSDv3, skipped match due to no LHS term candidates");
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
                auto mclVarIt = mcl->getVariableIterator();  // includes vars in rhs
                while (mclVarIt.hasNext()) {
                  unsigned int var = mclVarIt.next();
                  ASS(binder.isBound(var));
                }
                // VariableIterator rhsVarIt(rhs);
                // while (rhsVarIt.hasNext()) {
                //   TermList rhsVar = rhsVarIt.next();
                //   ASS(binder.isBound(rhsVar.var()));
                // }
                // this assertion is not really necessary... if it fails, it would fail in binder.applyTo below anyways... TODO: remove this block later
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
                //      eqLitS               dlit
                //    vvvvvvvvvvv          vvvvvvvv
                //    lhsS = rhsS \/ C     lhsS = t \/ CΘ \/ D
                //   ------------------------------------------
                //              rhsS = t \/ CΘ \/ D
                TermList t = EqHelper::getOtherEqualitySide(dlit, lhsS);
                if (t == rhsS) {
                  // in this case, eqLitS == dlit; and forward subsumption should have deleted the right premise already
                  ASS_EQ(binder.applyTo(eqLit), dlit);  // eqLitS == dlit
                  ASS(!getOptions().forwardSubsumption());  // Note that _doSubsumption can still be true here because MLMatcher2 might find an FSD-match before the FS-match
                  premises = pvi(getSingletonIterator(mcl));
                  env.statistics->forwardSubsumed++;
                  return true;
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
                RSTAT_CTR_INC("FSDv3, main premise not redundant");
                continue;
              }  // if (!_allowIncompleteness)
isRedundant:

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

              premises = pvi(getSingletonIterator(mcl));
              replacement = newCl;

#if FSD_LOG_INFERENCES
              env.beginOutput();
              env.out() << "\% Begin Inference \"FSDv3-" << newCl->number() << "\"\n";
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
              env.out() << "\% End Inference \"FSDv3-" << newCl->number() << "\"" << std::endl;
              env.endOutput();
#endif

              RSTAT_MCTR_INC("FSDv3, successes by MLMatch", numMatches + 1);  // +1 so it fits with the previous output

#if VDEBUG && FSD_VDEBUG_REDUNDANCY_ASSERTIONS
              if (getOptions().literalComparisonMode() != Options::LiteralComparisonMode::REVERSE) {  // see note above
                // Check newCl < cl.
                // This is quite obvious, there should be no problems with this.
                ASS(clauseIsSmaller(newCl->literals(), newCl->length(), cl->literals(), cl->length(), ordering));
                // Check mclΘ < cl.
                // This is not so clear and might easily be violated if we have a bug above.
                v_vector<Literal*> mclS(mcl->literals(), mcl->literals() + mcl->length());
                ASS_EQ(mcl->length(), mclS.size());
                for (auto it = mclS.begin(); it != mclS.end(); ++it) {
                  *it = binder.applyTo(*it);
                }
                if (!clauseIsSmaller(mclS.data(), mclS.size(), cl->literals(), cl->length(), ordering)) {
                  std::cerr << "FSDv3: redundancy violated!" << std::endl;
                  std::cerr << "mcl: " << mcl->toString() << std::endl;
                  std::cerr << " cl: " <<  cl->toString() << std::endl;
                  std::cerr << "mcl < cl required but it doesn't seem to be the case" << std::endl;
                  ASSERTION_VIOLATION;
                }
              }
#endif

              return true;
            }  // for (lhs)
          }  // while (nvi.hasNext())
        }  // for (dli)
      }  // for (numMatches)

      if (numMatches > 0) {
        RSTAT_CTR_INC("FSDv3, MLMatch but no FSD inference");
      }

    }  // while (rit.hasNext)
  }  // for (li)


  ////////////////////////////
  // Subsumption Resolution //
  ////////////////////////////

  if (_doSubsumptionResolution) {
    // Subsumption resolution with unit clauses
    for (unsigned li = 0; li < cl->length(); ++li) {
      Literal* resLit = (*cl)[li];  // resolved literal
      SLQueryResultIterator rit = _unitIndex->getGeneralizations(resLit, /* complementary = */ true, /* retrieveSubst = */ false);
      while (rit.hasNext()) {
        Clause* mcl = rit.next().clause;
        if (ColorHelper::compatible(cl->color(), mcl->color())) {
          Clause* resCl = generateSubsumptionResolutionClause(cl, resLit, mcl);
          env.statistics->forwardSubsumptionResolution++;
          premises = pvi(getSingletonIterator(mcl));
          replacement = resCl;
          return true;
        }
      }
    }

    // Subsumption resolution with clauses we've already prepared (during subsumption(demodulation) check)
    for (ClauseMatches const& cm : altsStorage) {
      Clause* mcl = cm.base();
      for (unsigned li = 0; li < cl->length(); ++li) {
        Literal* resLit = (*cl)[li];  // resolved literal
        if (ColorHelper::compatible(cl->color(), mcl->color()) && checkForSubsumptionResolution(cl, cm, resLit)) {
          Clause* resCl = generateSubsumptionResolutionClause(cl, resLit, mcl);
          env.statistics->forwardSubsumptionResolution++;
          premises = pvi(getSingletonIterator(mcl));
          replacement = resCl;
          return true;
        }
      }
    }

    // Subsumption resolution with remaining clauses.
    // New candidates must contain a generalization of the resolved literal
    // (because all others would have been tested already for subsumption above)
    for (unsigned li = 0; li < cl->length(); ++li) {
      Literal* resLit = (*cl)[li];  // resolved literal
      SLQueryResultIterator rit = _index->getGeneralizations(resLit, /* complementary = */ true, /* retrieveSubstitutions = */ false);
      while (rit.hasNext()) {
        SLQueryResult res = rit.next();
        Clause* mcl = res.clause;

        if (mcl->hasAux()) {
          // we have already examined this clause
          continue;
        }
        mcl->setAux(nullptr);

        ASS(dynamic_cast<FwSubsSimplifyingLiteralIndex*>(_index.get()) != nullptr);
        if (static_cast<FwSubsSimplifyingLiteralIndex*>(_index.get())->isSecondBest(res.clause, res.literal)) {  // FIXME
          continue;
        }

        altsStorage.emplace_back(mcl, cl_miniIndex);
        ClauseMatches const& cm = altsStorage.back();
        ASS_EQ(cm.base(), mcl);  // make sure we got the right one (since C++17, emplace_back returns the new element)

        if (ColorHelper::compatible(cl->color(), mcl->color()) && checkForSubsumptionResolution(cl, cm, resLit)) {
          Clause* resCl = generateSubsumptionResolutionClause(cl, resLit, mcl);
          env.statistics->forwardSubsumptionResolution++;
          premises = pvi(getSingletonIterator(mcl));
          replacement = resCl;
          return true;
        }
      }
    }
  } // if (_doSubsumptionResolution)


  ////////////////////
  // Not applicable //
  ////////////////////

  return false;
}
