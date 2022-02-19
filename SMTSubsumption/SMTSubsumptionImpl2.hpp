#ifndef SMTSUBSUMPTIONIMPL2_HPP
#define SMTSUBSUMPTIONIMPL2_HPP

#include "Kernel/Clause.hpp"
#include "Lib/STL.hpp"
#include "./subsat/subsat.hpp"

// The ground literal prefilter seems to slow us down slightly in general.
// Maybe it's more helpful with induction enabled? since that adds a lot of ground clauses.
#define GROUND_LITERAL_PREFILTER 0

namespace SMTSubsumption {

class SMTSubsumptionImpl2
{
  private:

#if 1
    template <typename T>
    using allocator_type = STLAllocator<T>;
#else
    template <typename T>
    using allocator_type = std::allocator<T>;
#endif

    subsat::Solver<allocator_type> solver;
    subsat::Solver<allocator_type>::BindingsManager bm;

#if GROUND_LITERAL_PREFILTER
    vvector<std::uint8_t> base_used;
    vvector<std::uint8_t> inst_used;
#endif

    Kernel::Clause* m_base = nullptr;
    Kernel::Clause* m_instance = nullptr;

    /// AtMostOne constraints stating that each instance literal may be matched at most once.
    vvector<subsat::AllocatedConstraintHandle> instance_constraints;

    /// Possibly resolved literals for subsumption resolution
    /// Entry: pair of boolean variable and index of the corresponding instance literal.
    vvector<std::pair<subsat::Var, std::uint32_t>> complementary_matches;

    // TODO: allocate this into one big array...
    vvector<vvector<subsat::Var>> inst_normal_matches;
    vvector<vvector<subsat::Var>> inst_compl_matches;
    vvector<subsat::Var> inst_is_compl_matched;

  public:
    CLASS_NAME(SMTSubsumptionImpl2);
    USE_ALLOCATOR(SMTSubsumptionImpl2);

    SMTSubsumptionImpl2();

    /// Set up the subsumption problem.
    /// Returns false if no solution is possible.
    /// Otherwise, solve() needs to be called.
    bool setupSubsumption(Kernel::Clause* base, Kernel::Clause* instance);

    /// Set up the subsumption resolution problem from scratch.
    /// Returns false if no solution is possible.
    /// Otherwise, solve() needs to be called.
    bool setupSubsumptionResolution(Kernel::Clause* base, Kernel::Clause* instance);

    /// Solve the subsumption instance created by the previous call to a setup... function.
    bool solve();

    /// Call this function after solve() has returned true for an SR instance
    Kernel::Clause* getSubsumptionResolutionConclusion();

    bool checkSubsumption(Kernel::Clause* base, Kernel::Clause* instance);

    /// For correctness checking: if the original subsumption resolution finds a conclusion, call this to check whether we can also find this conclusion.
    /// Note that SR is not unique, so there could be multiple possible conclusions, and both approaches may return a different one.
    ///
    /// Example for multiple possible subsumption resolutions:
    ///     base = P(x) \/ Q(x) \/ R(x)
    ///     inst = P(c) \/ Q(c) \/ ~R(c) \/ P(d) \/ ~Q(d) \/ R(d)
    ///
    /// Pass NULL for the conclusion to check that subsumption resolution isn't possible.
    bool checkSubsumptionResolution(Kernel::Clause* base, Kernel::Clause* instance, Kernel::Clause* conclusion);
};

}

#endif /* !SMTSUBSUMPTIONIMPL2_HPP */
