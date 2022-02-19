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



    struct BaseLitInfo {
    // CLASS_NAME(BaseLitInfo);
    // USE_ALLOCATOR(BaseLitInfo);
      subsat::Var first;  // first match
      uint32_t match_count;  // how many matches
      // one past the end
      subsat::Var var_end() const {
        return subsat::Var{first.index() + match_count};
      }
      subsat::Var compl_first;  // first complementary match
      uint32_t compl_match_count;  // how many matches
      // one past the end
      subsat::Var compl_var_end() const {
        return subsat::Var{compl_first.index() + compl_match_count};
      }
    };

    struct MatchCache {
      CLASS_NAME(MatchCache);
      USE_ALLOCATOR(MatchCache);

      BindingsManager bm;
      vvector<BaseLitInfo> bli;  // index is the index of the base literal; size tells us how many base literals we matched (in case of early exit during subsumption)
      uint32_t zero_match_count = 0;  // how many base literals without any matches
      uint32_t zero_match_header = std::numeric_limits<uint32_t>::max();
      // [j] how many times an instance literal is matched
      // [j+inst_len] how many times an instance literal is compl-matched
      // (later converted to indices via computing the running sum)
      vvector<uint32_t> inst_match_count;
      #ifndef NDEBUG
      Kernel::Clause* base = nullptr;
      Kernel::Clause* inst = nullptr;
      #endif

      MatchCache() = default;

      void clear() {
        bm.clear();
        bli.clear();
        zero_match_count = 0;
        zero_match_header = std::numeric_limits<uint32_t>::max();
        inst_match_count.clear();
      #ifndef NDEBUG
        base = nullptr;
        inst = nullptr;
      #endif
      }

      bool empty() {
        return bm.empty() && bli.empty();
      }
    };

    vvector<MatchCache*> mcs;
    MatchCache shared_mc;  // for when we don't have a cached one
    unsigned next_mc;



    Solver solver;

    Kernel::Clause* instance = nullptr;   // main premise for forward subsumption (resolution)

    // /// AtLeastOne constraints stating that each base literal may be matched at least once.
    // /// Since we allocate SAT variables consecutively, we only need to store the length of each of these clauses.
    // vvector<uint32_t> base_clauses;

    /// AtMostOne constraints stating that each instance literal may be matched at most once.
    vvector<subsat::AllocatedConstraintHandle> instance_constraints;

    // NOTE: we use the default_init_allocator to avoid zero-initialization when resizing
    /// match variables sorted by instance literal
    /// inst[0] matches | inst[1] matches | ... | inst[0] compl_matches | inst[1] compl_matches | ...
    std::vector<uint32_t, default_init_allocator<uint32_t, allocator_type<uint32_t>>> m_inst_matches;

    void fillMatches(MatchCache& mc, Kernel::Clause* base);
    void endMainPremise();

  public:
    CLASS_NAME(SMTSubsumptionImpl3);
    USE_ALLOCATOR(SMTSubsumptionImpl3);

    SMTSubsumptionImpl3();
    ~SMTSubsumptionImpl3();

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
