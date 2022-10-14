#ifndef SATSUBSUMPTIONIMPL3_HPP
#define SATSUBSUMPTIONIMPL3_HPP

#include "Kernel/Clause.hpp"
#include "Lib/STL.hpp"
#include "./subsat/subsat.hpp"


#define SUBSAT_SOLVER_REUSE 1


namespace SATSubsumption {

class SATSubsumptionImpl3;

class SATSubsumptionImpl3_Token {
  SATSubsumptionImpl3* impl;
  SATSubsumptionImpl3_Token(SATSubsumptionImpl3& impl) : impl(&impl) {}
  friend class SATSubsumptionImpl3;
public:
  CLASS_NAME(SATSubsumptionImpl3_Token);
  USE_ALLOCATOR(SATSubsumptionImpl3_Token);
  SATSubsumptionImpl3_Token(SATSubsumptionImpl3_Token&& other) : impl(std::exchange(other.impl, nullptr)) {}
  ~SATSubsumptionImpl3_Token();
};

class SATSubsumptionImpl3
{
  private:

#if 1
    template <typename T>
    using allocator_type = STLAllocator<T>;
#else
    template <typename T>
    using allocator_type = std::allocator<T>;
#endif

    using Token = SATSubsumptionImpl3_Token;
    friend class SATSubsumptionImpl3_Token;
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
      CLASS_NAME(SATSubsumptionImpl3::MatchCache);
      USE_ALLOCATOR(SATSubsumptionImpl3::MatchCache);

      BindingsManager bm;
      vvector<BaseLitInfo> bli;  // index is the index of the base literal; size tells us how many base literals we matched (in case of early exit during subsumption)
      uint32_t zero_match_count = 0;  // how many base literals without any matches; UINT_MAX means already checked for SR, nothing more to do.
      uint32_t zero_match_header = std::numeric_limits<uint32_t>::max();
      // [j] how many times an instance literal is matched
      // [j+inst_len] how many times an instance literal is compl-matched
      // (later converted to indices via computing the running sum)
      vvector<uint32_t> inst_match_count;
      bool done = false;
#ifndef NDEBUG
      Kernel::Clause* base = nullptr;
      Kernel::Clause* inst = nullptr;
#endif

      MatchCache() {
        bli.reserve(8);
        inst_match_count.reserve(64);
      }

      void clear() {
        bm.clear();
        bli.clear();
        zero_match_count = 0;
        zero_match_header = std::numeric_limits<uint32_t>::max();
        inst_match_count.clear();
        done = false;
#ifndef NDEBUG
        base = nullptr;
        inst = nullptr;
#endif
      }

      bool empty() {
        return bm.empty() && bli.empty();
      }
    };

    // just to satisfy Vampire's custom allocator
    struct SolverWrapper {
      CLASS_NAME(SATSubsumptionImpl3::SolverWrapper);
      USE_ALLOCATOR(SATSubsumptionImpl3::SolverWrapper);
      Solver s;
    };

    // TODO: move MatchCache to cpp file; use std::unique_ptr in mcs and shared_mc.
    vvector<MatchCache*> mcs;
    MatchCache shared_mc;  // for when we don't have a cached one
    unsigned next_mc;
    MatchCache* last_mc;

    std::unique_ptr<SolverWrapper> shared_solver;

    void recreate_solver();

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
    CLASS_NAME(SATSubsumptionImpl3);
    USE_ALLOCATOR(SATSubsumptionImpl3);

    SATSubsumptionImpl3();
    ~SATSubsumptionImpl3();

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

    /// Call this function after solve() has returned true for an SR instance
    Kernel::Clause* getSubsumptionResolutionConclusion(Kernel::Clause* base);

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

#endif /* !SATSUBSUMPTIONIMPL3_HPP */
