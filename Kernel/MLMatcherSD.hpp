/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __MLMatcherSD__
#define __MLMatcherSD__

#include "Clause.hpp"
#include "Forwards.hpp"
#include "Lib/STL.hpp"

namespace Kernel {

using namespace Lib;


/**
 * MLMatcherSD implements a solver for the subsumption-demodulation match problem,
 * an extension of the multi-literal match problem (see MLMatcher.hpp).
 *
 * Input: two clauses, a base clause C and an instance clause D.
 * Question: Is there a positive equality literal L in C and a substitution θ such that (C \ {L})θ is a submultiset of D?
 *
 * This is needed by ForwardSubsumptionDemodulation and BackwardSubsumptionDemodulation.
 */
class MLMatcherSD final
{
  public:
    /**
     * Constructs an MLMatcherSD and puts it in an invalid state.
     */
    MLMatcherSD();

    ~MLMatcherSD();

    /**
     * Initializes the matcher to the given match problem.
     * The matcher will be in a valid (but unmatched) state.
     *
     * MLMatcherSD solves the SD-Match-Problem:
     * - One positive equality of the baseLits is selected for demodulation, and
     * - All other literals are (multiset-)matched to the given alts from the instance
     *   (may involve a uniform substitution from base to alts/instance).
     *
     * Preconditions:
     * - baseLits must have length baseLen
     * - alts must have length baseLen (for 0 <= bi < baseLen, the literal baseLits[bi] will be matched against the alternatives in the list alts[bi])
     * - All literals in 'alts' must appear in 'instance'
     * - 'instance' must not have duplicate literals (during normal operation this is ensured by Inferences::DuplicateLiteralRemovalISE)
     */
    void init(Literal** baseLits,
              unsigned baseLen,
              Clause* instance,
              LiteralList const* const *alts);

    void init(Clause* base, Clause* instance, LiteralList const* const *alts)
    {
      init(base->literals(), base->length(), instance, alts);
    }

    /**
     * Finds the next match.
     * May only be called if the matcher is in a valid state.
     * Return value:
     * - True if a match was found. The matcher is now in a valid and matched state.
     * - False if no more matches are possible. The matcher is now in an invalid state.
     */
    bool nextMatch();

    /**
     * Returns the equality literal from base that was selected for demodulation.
     * May only be called in a matched state (i.e., after nextMatch() has returned true).
     * May return nullptr in case of subsumption (i.e., complete multiset match).
     */
    Literal* getEqualityForDemodulation() const;

    /**
     * Returns a bitmap that indicates which alts are currently matched by some base literal.
     * May only be called in a matched state (i.e., after nextMatch() has returned true).
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
    MLMatcherSD(MLMatcherSD const&) = delete;
    MLMatcherSD& operator=(MLMatcherSD const&) = delete;

    // Moving works by moving the pointer m_impl
    MLMatcherSD(MLMatcherSD&&) noexcept;
    MLMatcherSD& operator=(MLMatcherSD&&) noexcept;

  private:
    class Impl;
    std::unique_ptr<Impl> m_impl;
};


};

#endif /* __MLMatcherSD__ */
