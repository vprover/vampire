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
 * @file MLMatcher.hpp
 * Defines class MLMatcher with methods
 * supporting multiliteral matching.
 */

#ifndef __MLMatcher__
#define __MLMatcher__

#include "Clause.hpp"
#include "Forwards.hpp"
#include "Lib/STL.hpp"

namespace Kernel {

using namespace Lib;


/**
 * MLMatcher implements a solver for the multi-literal match problem.
 *
 * Input: two clauses, a base clause C and an instance clause D.
 * Question: Does a substitution θ exist such that Cθ is a subset (or submultiset) of D?
 */
class MLMatcher
{
  private:
    /**
     * Initializes the matcher to the given match problem.
     * The matcher will be in a valid (but unmatched) state.
     *
     * Preconditions:
     * - baseLits must have length baseLen
     * - alts must have length baseLen (for 0 <= bi < baseLen, the literal baseLits[bi] will be matched against the alternatives in the list alts[bi])
     * - All literals in 'alts' must appear in 'instance'.
     * - If resolvedLit is not null, multiset must be false. (Hypothesis; not 100% sure if the matching algorithm breaks in that case)
     */
    void init(Literal** baseLits,
              unsigned baseLen,
              Clause* instance,
              LiteralList const* const *alts,
              Literal* resolvedLit,
              bool multiset);

  public:
    /**
     * Constructs an MLMatcher and puts it in an invalid state.
     */
    MLMatcher();

    void init(Literal** baseLits, unsigned baseLen, Clause* instance, LiteralList const* const *alts, bool multiset = false)
    {
      init(baseLits, baseLen, instance, alts, nullptr, multiset);
    }

    void init(Clause* base, Clause* instance, LiteralList const* const *alts, bool multiset = false)
    {
      init(base->literals(), base->length(), instance, alts, multiset);
    }

    void init(Literal** baseLits, unsigned baseLen, Clause* instance, LiteralList const* const *alts, Literal* resolvedLit)
    {
      // NOTE: we need multiset matching for subsumption, but for subsumption resolution it is not necessary
      init(baseLits, baseLen, instance, alts, resolvedLit, resolvedLit == nullptr);
    }

    void init(Clause* base, Clause* instance, LiteralList const* const *alts, Literal* resolvedLit)
    {
      init(base->literals(), base->length(), instance, alts, resolvedLit);
    }

    ~MLMatcher();

    /**
     * Finds the next match.
     * May only be called if the matcher is in a valid state.
     * Return value:
     * - True if a match was found. The matcher is now in a valid and matched state.
     * - False if no more matches are possible. The matcher is now in an invalid state.
     */
    bool nextMatch();

    /**
     * Returns a bitmap that indicates which alts are currently matched by some base literal.
     * May only be called in a matched state (i.e., after nextMatch() has returned true).
     * May only be called if the matcher was initialized with resolvedLit == nullptr.
     *
     * After the function returns:
     * outMatchedBitmap[i] == true iff instance[i] is matched by some literal of base
     *
     * The given vector will be cleared before operating on it.
     */
    void getMatchedAltsBitmap(vvector<bool>& outMatchedBitmap) const;

    /**
     * Returns the variable bindings due to the current match.
     * May only be called in a matched state (i.e., after nextMatch() has returned true).
     */
    void getBindings(vunordered_map<unsigned, TermList>& outBindings) const;

    // Disallow copy because the internal implementation still uses pointers to the underlying storage and it seems hard to untangle that.
    MLMatcher(MLMatcher const&) = delete;
    MLMatcher& operator=(MLMatcher const&) = delete;

    // Moving works by moving the pointer m_impl
    MLMatcher(MLMatcher&&) = default;
    MLMatcher& operator=(MLMatcher&&) = default;

  private:
    class Impl;
    std::unique_ptr<Impl> m_impl;

  public:
    /// Helper function for compatibility to previous code. It uses a shared static instance of MLMatcher::Impl.
    static bool canBeMatched(Literal** baseLits, unsigned baseLen, Clause* instance, LiteralList const* const *alts, Literal* resolvedLit, bool multiset);

    /// Helper function for compatibility to previous code. It uses a shared static instance of MLMatcher::Impl.
    static bool canBeMatched(Clause* base,                          Clause* instance, LiteralList const* const *alts, Literal* resolvedLit)
    {
      return canBeMatched(base->literals(), base->length(), instance, alts, resolvedLit, resolvedLit == nullptr);
    }
};


};

#endif /* __MLMatcher__ */
