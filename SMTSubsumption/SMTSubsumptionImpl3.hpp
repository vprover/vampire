#ifndef SMTSUBSUMPTIONIMPL3_HPP
#define SMTSUBSUMPTIONIMPL3_HPP

#include "Kernel/Clause.hpp"
#include "Lib/STL.hpp"
#include "./subsat/subsat.hpp"

namespace SMTSubsumption {

class SMTSubsumptionImpl3
{
  private:

#if 1
    template <typename T>
    using allocator_type = STLAllocator<T>;
#else
    template <typename T>
    using allocator_type = std::allocator<T>;
#endif

    using Solver = subsat::Solver<allocator_type>;
    using BindingsManager = typename Solver::BindingsManager;

    Solver solver;
    vvector<BindingsManager> bms;
    unsigned next_bm;

    Kernel::Clause* instance = nullptr;   // main premise for forward subsumption (resolution)

    /// AtLeastOne constraints stating that each base literal may be matched at least once.
    /// Since we allocate SAT variables consecutively, we only need to store the length of each of these clauses.
    vvector<uint32_t> base_clauses;

    /// AtMostOne constraints stating that each instance literal may be matched at most once.
    vvector<subsat::AllocatedConstraintHandle> instance_constraints;

    void endMainPremise();

  public:
    CLASS_NAME(SMTSubsumptionImpl3);
    USE_ALLOCATOR(SMTSubsumptionImpl3);

    SMTSubsumptionImpl3();

    class Token {
      SMTSubsumptionImpl3& impl;
      Token(SMTSubsumptionImpl3& impl) : impl(impl) {}
      friend class SMTSubsumptionImpl3;
    public:
      ~Token();
    };

    /// Set up forward subsumption and subsumption resolution for the given main premise.
    /// Hold on to the returned token until done.
    NODISCARD Token setupMainPremise(Kernel::Clause* new_instance);

    /// Set up the subsumption problem. Must have called setupMainPremise first.
    /// Returns false if no solution is possible.
    /// Otherwise, solve() needs to be called.
    bool setupSubsumption(Kernel::Clause* base);

    /// Set up the subsumption resolution problem. Must have called setupMainPremise first.
    /// Returns false if no solution is possible.
    /// Otherwise, solve() needs to be called.
    bool setupSubsumptionResolution(Kernel::Clause* base);

    bool solve();
};

}

#endif /* !SMTSUBSUMPTIONIMPL3_HPP */
