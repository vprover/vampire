/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef SUBSUMPTIONDEMODULATIONHELPER_HPP
#define SUBSUMPTIONDEMODULATIONHELPER_HPP

#include "Indexing/LiteralMiniIndex.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Term.hpp"
#include "Lib/STL.hpp"



// Set to true to output FSD inferences on stdout
#define FSD_LOG_INFERENCES false

// Set to true to check redundancy of FSD main premise in debug mode
#define FSD_VDEBUG_REDUNDANCY_ASSERTIONS true


// Set to true to output BSD inferences on stdout
#define BSD_LOG_INFERENCES false

// Set to true to check redundancy of BSD main premise in debug mode
#define BSD_VDEBUG_REDUNDANCY_ASSERTIONS true



namespace Inferences {

using namespace Indexing;
using namespace Kernel;
using namespace Lib;



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
  CLASS_NAME(OverlayBinder);
  USE_ALLOCATOR(OverlayBinder);

  public:
    using Var = unsigned int;
    using BindingsMap = vunordered_map<Var, TermList>;

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

    bool isBound(Var var) const
    {
      return m_base.find(var) != m_base.end()
        || m_overlay.find(var) != m_overlay.end();
    }

    void specVar(Var var, TermList term) const
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
      UnboundVariableOffsetApplicator applicator(*this, unboundVarOffset);
      return SubstHelper::apply(t, applicator, noSharing);
    }

  public:
    class UnboundVariableOffsetApplicator
    {
      public:
        UnboundVariableOffsetApplicator(OverlayBinder const& binder, Var unboundVarOffset)
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

std::ostream& operator<<(std::ostream& o, OverlayBinder const& binder);


/**
 * Stores an instance of the multi-literal matching problem.
 * Allows us to re-use the alts from subsumption for subsumption resolution.
 */
class SDClauseMatches
{
  CLASS_NAME(SDClauseMatches);
  USE_ALLOCATOR(SDClauseMatches);

  public:
    // required to use std::vector::emplace_back
    DECLARE_PLACEMENT_NEW;

  public:
    SDClauseMatches(Clause* base, LiteralMiniIndex const& ixAlts);

    ~SDClauseMatches();

    // Disallow copy
    SDClauseMatches(SDClauseMatches const&) = delete;
    SDClauseMatches& operator=(SDClauseMatches const&) = delete;

    // Default move is fine
    SDClauseMatches(SDClauseMatches&&) = default;
    SDClauseMatches& operator=(SDClauseMatches&&) = default;

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
    vvector<LiteralList*> m_alts;
    unsigned m_basePosEqs;
    unsigned m_baseLitsWithoutAlts;
    unsigned m_basePosEqsWithoutAlts;
};  // class SDClauseMatches


class SDHelper
{
  public:
    static bool checkForSubsumptionResolution(Clause* cl, SDClauseMatches const& cm, Literal* resLit);
    static Clause* generateSubsumptionResolutionClause(Clause* cl, Literal* resLit, Clause* mcl);

#if VDEBUG  // these function are slow and should only be used in debug mode
  private:
    enum class ClauseComparisonResult
    {
      Smaller,
      Equal,
      GreaterOrIncomparable
    };

    static ClauseComparisonResult clauseCompare(Literal* const lits1[], unsigned n1, Literal* const lits2[], unsigned n2, Ordering const& ordering);

    /// Compares mclΘ to cl.
    template <typename Applicator>
    static ClauseComparisonResult substClauseCompare(Clause* mcl, Applicator const& applicator, Clause* cl, Ordering const& ordering)
    {
      vvector<Literal*> mclS(mcl->literals(), mcl->literals() + mcl->length());
      ASS_EQ(mcl->length(), mclS.size());
      for (auto it = mclS.begin(); it != mclS.end(); ++it) {
        *it = applicator.applyTo(*it);
      }
      return SDHelper::clauseCompare(mclS.data(), mclS.size(), cl->literals(), cl->length(), ordering);
    }

  public:
    /// Returns true iff clause with literal lits1 is smaller than clause with literals lits2
    /// in the multiset extension of the given ordering.
    static bool clauseIsSmaller(Literal* const lits1[], unsigned n1, Literal* const lits2[], unsigned n2, Ordering const& ordering)
    {
      return clauseCompare(lits1, n1, lits2, n2, ordering) == ClauseComparisonResult::Smaller;
    }

    /// Returns true iff mcl < cl.
    static bool clauseIsSmaller(Clause* mcl, Clause* cl, Ordering const& ordering)
    {
      return SDHelper::clauseIsSmaller(mcl->literals(), mcl->length(), cl->literals(), cl->length(), ordering);
    }

    /// Returns true iff mclΘ < cl,
    /// where the substitution Θ is given as applicator (cf. class SubstHelper).
    template <typename Applicator>
    static bool substClauseIsSmaller(Clause* mcl, Applicator const& applicator, Clause* cl, Ordering const& ordering)
    {
      return SDHelper::substClauseCompare(mcl, applicator, cl, ordering) == ClauseComparisonResult::Smaller;
    }

    /// Returns true iff mclΘ <= cl,
    /// where the substitution Θ is given as applicator (cf. class SubstHelper).
    template <typename Applicator>
    static bool substClauseIsSmallerOrEqual(Clause* mcl, Applicator const& applicator, Clause* cl, Ordering const& ordering)
    {
      auto result = SDHelper::substClauseCompare(mcl, applicator, cl, ordering);
      return result == ClauseComparisonResult::Smaller || result == ClauseComparisonResult::Equal;
    }
#endif
};


/**
 * Returns true iff termθ contains all variables that otherθ contains (possibly more).
 *
 * The substitution θ is given as an applicator, cf. class SubstHelper.
 * An applicator is an object with a method of the following signature:
 *    TermList apply(unsigned int var);
 */
template <typename Applicator>
bool termContainsAllVariablesOfOtherUnderSubst(TermList term, TermList other, Applicator const& applicator)
{
  CALL("termContainsAllVariablesOfOtherUnderSubst");

  static vunordered_set<unsigned int> vars(16);
  vars.clear();

  static VariableIterator vit;
  static VariableIterator vit2;

  // collect term's vars after substitution
  vit.reset(term);
  while (vit.hasNext()) {
    TermList t = applicator.apply(vit.next().var());
    vit2.reset(t);
    while (vit2.hasNext()) {
      vars.insert(vit2.next().var());
    }
  }

  // check that all vars of other after substition have been collected
  vit.reset(other);
  while (vit.hasNext()) {
    TermList t = applicator.apply(vit.next().var());
    vit2.reset(t);
    while (vit2.hasNext()) {
      if (vars.find(vit2.next().var()) == vars.end()) {
#if VDEBUG
        {
          TermList termS = SubstHelper::apply(term, applicator, /* no sharing = */ true);
          TermList otherS = SubstHelper::apply(other, applicator, /* no sharing = */ true);
          ASS(!termS.containsAllVariablesOf(otherS));
          if (termS.isTerm()) { termS.term()->destroyNonShared(); }
          if (otherS.isTerm()) { otherS.term()->destroyNonShared(); }
        }
#endif
        return false;
      }
    }
  }

#if VDEBUG
  {
      TermList termS = SubstHelper::apply(term, applicator, /* no sharing = */ true);
      TermList otherS = SubstHelper::apply(other, applicator, /* no sharing = */ true);
      ASS(termS.containsAllVariablesOf(otherS));
      if (termS.isTerm()) { termS.term()->destroyNonShared(); }
      if (otherS.isTerm()) { otherS.term()->destroyNonShared(); }
  }
#endif
  return true;
}


};

#endif /* !SUBSUMPTIONDEMODULATIONHELPER_HPP */
