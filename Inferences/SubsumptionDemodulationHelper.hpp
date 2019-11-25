#ifndef SUBSUMPTIONDEMODULATIONHELPER_HPP
#define SUBSUMPTIONDEMODULATIONHELPER_HPP

#include "Indexing/LiteralMiniIndex.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/Term.hpp"
#include "Lib/STL.hpp"


namespace Inferences {

using namespace Indexing;
using namespace Kernel;
using namespace Lib;


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


class SDHelper
{
  public:
    static bool checkForSubsumptionResolution(Clause* cl, ClauseMatches const& cm, Literal* resLit);
    static Clause* generateSubsumptionResolutionClause(Clause* cl, Literal* resLit, Clause* mcl);

#if VDEBUG
    /// Returns true iff clause with literal lits1 is smaller than clause with literals lits2
    /// in the multiset extension of the given ordering.
    static bool clauseIsSmaller(Literal* const lits1[], unsigned n1, Literal* const lits2[], unsigned n2, Ordering const& ordering);
#endif
};


};

#endif /* !SUBSUMPTIONDEMODULATIONHELPER_HPP */
