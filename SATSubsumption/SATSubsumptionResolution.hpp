#ifndef SAT_SUBSUMPTION_RESOLUTION_HPP
#define SAT_SUBSUMPTION_RESOLUTION_HPP

#include "Kernel/Clause.hpp"
#include "Lib/STL.hpp"
#include "./subsat/subsat.hpp"

// TODO : remove that when the real VTEST flag is added
#define VTEST


namespace SMTSubsumption {
class SATSubsumption;

class SATSubsumption
{
  #ifdef VTEST
  // Make it public to allow unit testing
  public :
  #else
  private:
  #endif
    template <typename T>
    using allocator_type = STLAllocator<T>;
    using Solver = subsat::Solver<allocator_type>;
    using BindingsManager = typename Solver::BindingsManager;

    // just to satisfy Vampire's custom allocator
    struct SolverWrapper {
      CLASS_NAME(SATSubsumption::SolverWrapper);
      USE_ALLOCATOR(SATSubsumption::SolverWrapper);
      Solver s;
    };

    /**
     * A Match represents a binding between two literals of different clauses.
     * The binding can be either positive or negative
     */
    struct Match {
      CLASS_NAME(SATSubsumption::Match);
      USE_ALLOCATOR(SATSubsumption::Match);
      // The index of the literal in the base clause
      unsigned _baseLitIndex;
      // The index of the literal in the instance clause
      unsigned _instanceLitIndex;
      // The polarity of the match (true for positive, false for negative)
      bool _isPositive;
      // The variable associated in the sat solver
      subsat::Var _satVar;

      Match() :
        _baseLitIndex(0),
        _instanceLitIndex(0),
        _isPositive(false),
        _satVar(subsat::Var(0)) {}

      Match(unsigned baseLitIndex, unsigned instanceLitIndex, bool isPositive, subsat::Var satVar) :
        _baseLitIndex(baseLitIndex),
        _instanceLitIndex(instanceLitIndex),
        _isPositive(isPositive),
        _satVar(satVar) {}

      std::string toString() const {
        return "Match(" + to_string(_baseLitIndex) + ", " + to_string(_instanceLitIndex) + ", " + to_string(_isPositive) + ", " + to_string(_satVar.index
        ()) + ")";
      }
    };

    /**
     * A Match set is a facitlity to store matches, and enumerate them either according to the base clause or the instance clause indices.
     *
     */
    struct MatchSet {
      CLASS_NAME(SATSubsumption::MatchSet);
      USE_ALLOCATOR(SATSubsumption::MatchSet);
      friend struct Match;

      /// @brief for each literal in the base clause, holds a list of matches to the instance clause
      /// _i_matches[i] holds the list of matches for the i'th literal in the base clause
      /// the list is not stored in any particular order
      vvector<vvector<Match*>> _i_matches;
      /// @brief for each literal in the instance clause, holds a list of matches to the base clause
      /// _j_matches[j] holds the list of matches for the j'th literal in the instance clause
      /// the list is not stored in any particular order
      vvector<vvector<Match*>> _j_matches;

      /// @brief Remembers whether some positive match or negative match was found for each literal in the base clause
      /// - 0 -> no match
      /// - 1 -> positive match
      /// - 2 -> negative match
      /// - 3 -> both positive and negative match
      /// @remark
      /// Add a positive match : |= 01
      /// Add a negative match : |= 10
      /// Since we only need 2 bits, 4 values fit in one byte
      /// j -> j/4 -> j >> 2*j%4
      /// 00011000, j=0 -> 00, j=1 -> 10,...
      /// 3 2 1 0
      vvector<uint8_t> _i_matcheState;
      vvector<uint8_t> _j_matcheState;

      /// @brief the number literals in the base clause
      unsigned _nBaseLits;
      /// @brief the number literals in the instance clause
      unsigned _nInstanceLits;

      /// @brief vector of matches used to associate a sat variable index to a match
      vvector<Match*> _varToMatch;
      /// @brief the number of matches currently at use
      unsigned _nUsedMatches;
      /// @brief the number of matches currently allocated
      unsigned _nAllocatedMatches;
      /// @brief the matches available for use
      /// This is used to avoid allocating and deallocating memory at each resolutiton check
      /// The memory is allocated by batches of powers of 2
      /// In the order of allocations, we would have :
      /// 0 1 1 2 2 2 2 3 3 3 3 3 3 3 3 ...
      /// ^ ^   ^       ^               ^
      /// such that we have to free the memory only at the start of the next batch (i.e. at position 0, 1, 3, 7... = 2^k - 1)
      /// It is therefore important to start allocating at 1.
      Match **_allocatedMatches;

      /**
       * Creates a new match set for the given base and instance clauses
       * Allocates memory for 1 Match
       *
       * @param base the base clause
       * @param instance the instance clause
       */
      MatchSet(unsigned nBaseLits, unsigned nInstanceLits);

      ~MatchSet();

      /**
       * Returns one Match from the pool of available matches
       * or allocates more memory and returns one of the newly allocated matches
       */
      Match* allocateMatch();

      /**
       * Resizes the match vectors to the given size
       * Garantees that the a match can be added at index ( @b nBaseLits - 1, @b nInstanceLits - 1 )
       *
       * Warning, if any dimension is shrinked, the matches may be lost.
       */
      void resize(unsigned nBaseLits, unsigned nInstanceLits);

      /**
       * Adds a new match to the set
       *
       * Assumes that the match was allocated by allocateMatch()
       *
       * @param match the match to add
       */
      void addMatch(Match *match);

      /**
       * Returns the vector of matches for the given literal in the base clause.
       * The vectors should not be modified
       * @param baseLitIndex the index of the literal in the base clause
       */
      vvector<Match*>& getMatchesForBaseLit(unsigned baseLitIndex);

      bool hasPositiveMatchForBaseLit(unsigned baseLitIndex);

      bool hasNegativeMatchForBaseLit(unsigned baseLitIndex);

      /**
       * Returns the vector of matches for the given literal in the instance clause.
       * The vectors should not be modified
       * @param instanceLitIndex the index of the literal in the instance clause
       */
      vvector<Match*>& getMatchesForInstanceLit(unsigned instanceLitIndex);

      bool hasPositiveMatchForInstanceLit(unsigned instanceLitIndex);

      bool hasNegativeMatchForInstanceLit(unsigned instanceLitIndex);

      /**
       * Returns all the used matches
       *
       * Warning : Any match allocated by the match set is returned, even if it was not added to the set yet.
       *
       * TODO Add safety check in debug mode
       */
      vvector<Match*> getAllMatches();

      /**
       * Returns the match for a given variable
       * @param v the variable
       * @return the match for the variable, or nullptr if no match exists
       */
      Match* getMatchForVar(subsat::Var v);

      /**
       * Clears the match set
       */
      void clear();
    };

    /* Variables */

    /// @brief the base clause
    Kernel::Clause *_base;
    /// @brief the instance clause
    Kernel::Clause *_instance;
    /// @brief the number of literals in the base clause
    unsigned _nBaseLits;
    /// @brief the number of literals in the instance clause
    unsigned _nInstanceLits;
    /// @brief the SAT solver
    SolverWrapper *_solver;
    /// @brief the bindings manager
    BindingsManager *_bindingsManager;
    /// @brief a vector used to store the sat variables that are subjected to the at most one constraint (will hold the c_j)
    /// The unsigned value is the index of the literal in the instance clause
    vvector<std::pair<unsigned, subsat::Var>> _atMostOneVars;
    //vvector<subsat::Var> _atMostOneVars;
    /// @brief the match set used to store the matches between the base and instance clauses
    MatchSet _matchSet;
    /// @brief model of the SAT solver
    vvector<subsat::Lit> _model;

    /* Methods */

    /// Set up the subsumption resolution problem. Must have called setupMainPremise first.
    /// Returns false if no solution is possible.
    /// Otherwise, solve() needs to be called.
    bool setupSubsumptionResolution(Kernel::Clause* base, Kernel::Clause* instance);

    /// @brief Adds one binding to the SAT solver and the match set
    /// @param binder the binder between the literals
    /// @param varNumber the variable number of the binder
    /// @param i the index of the literal in the base clause
    /// @param j the index of the literal in the instance clause
    void addBinding(BindingsManager::Binder *binder, unsigned varNumber, unsigned i, unsigned j, bool isPositive);

    /// Fills the MatchSet with the matches between the base and instance clauses
    /// Also fills the bindings manager with the bindings between the literals of the base and instance clauses
    /// Returns the number of variables added to the SAT solver
    /// Returns 0 if no solution is possible
    unsigned fillMatches();

    /// Call this function after solve() has returned true for an SR instance
    /// Returns a the clause that will replace instance
    Kernel::Clause* generateConclusion();


  public:
    CLASS_NAME(SATSubsumption);
    USE_ALLOCATOR(SATSubsumption);

    SATSubsumption();
    ~SATSubsumption();

    ///
    bool checkSubsumption(Kernel::Clause* base, Kernel::Clause* instance);

    /// For correctness checking: if the original subsumption resolution finds a conclusion, call this to check whether we can also find this conclusion.
    /// Note that SR is not unique, so there could be multiple possible conclusions, and both approaches may return a different one.
    ///
    /// Example for multiple possible subsumption resolutions:
    ///     base = P(x) \/ Q(x) \/ R(x)
    ///     inst = P(c) \/ Q(c) \/ ~R(c) \/ P(d) \/ ~Q(d) \/ R(d)
    ///
    /// Pass NULL for the conclusion to check that subsumption resolution isn't possible.
    Kernel::Clause* checkSubsumptionResolution(Kernel::Clause* base, Kernel::Clause* instance);

    void clear();
};

}

#endif /* !SAT_SUBSUMPTION_RESOLUTION_HPP */
