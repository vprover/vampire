#ifndef SAT_SUBSUMPTION_RESOLUTION_HPP
#define SAT_SUBSUMPTION_RESOLUTION_HPP

#include "Kernel/Clause.hpp"
#include "Lib/STL.hpp"
#include "./subsat/subsat.hpp"

/// @todo TODO : remove that when the real VTEST flag is added
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
     * A Match represents a binding between two literals L_i and M_j of different clauses L and M.
     * The binding can be either positive or negative
     */
    struct Match {
      CLASS_NAME(SATSubsumption::Match);
      USE_ALLOCATOR(SATSubsumption::Match);
      // The index of the literal in L (base clause for subsumption resolution)
      unsigned _i;
      // The index of the literal in M (instance clause for subsumption resolution)
      unsigned _j;
      // The polarity of the match (true for positive, false for negative)
      bool _polarity;
      // The variable associated in the sat solver
      subsat::Var _var;

      Match() :
        _i(0),
        _j(0),
        _polarity(true),
        _var(subsat::Var(0)) {}

      Match(unsigned baseLitIndex, unsigned instanceLitIndex, bool isPositive, subsat::Var satVar) :
        _i(baseLitIndex),
        _j(instanceLitIndex),
        _polarity(isPositive),
        _var(satVar) {}

      std::string toString() const {
        return "Match(" + to_string(_i) + ", " + to_string(_j) + ", " + to_string(_polarity) + ", " + to_string(_var.index
        ()) + ")";
      }
    };

    /**
     * A Match set is a facitlity to store matches, and allows to ennumerate them either according to the clause L or M indices.
     * The Match Set, when filled contains all the bindings possible between the clauses L and M
     * The match set can be abstracted as a sparse matrix holding the associated sat variable and polarity of the matches
     *
     * @example For example, here is a table of matches (not necessarily coherent with the subsumption resolutio problem)
     *
     *      i=0  i=1  i=2  i=3  i=4
     * j=0 | 0+ |    |    | 3- |    |
     *     --------------------------
     * j=1 |    | 1+ |    | 2+ |    |
     *     --------------------------
     * j=2 | 4- |    |    |    |    |
     *     --------------------------
     * j=3 |    |    | 5+ |    | 6- |
     *     --------------------------
     * j=4 |    | 7+ |    | 8- |    |
     *
     * The Match set allows to get a line or column of the matrix
     */
    struct MatchSet {
      CLASS_NAME(SATSubsumption::MatchSet);
      USE_ALLOCATOR(SATSubsumption::MatchSet);
      friend struct Match;

      /// @brief Holds the matches grouped by _i
      /// _iMatches[i] holds the list of matches for the i'th literal in L
      /// the list is stored in the order in which they are added to the set
      vvector<vvector<Match*>> _iMatches;
      /// @brief Holds the matches grouped by _j
      /// _jMatches[j] holds the list of matches for the j'th literal in M
      /// the list is stored in the order in which they are added to the set
      vvector<vvector<Match*>> _jMatches;

      /// @brief Metadata remembering whether some positive match or negative match was found for each literal in L
      /// @remark
      /// This information only needs 2 bits
      /// - 00 -> no match
      /// - 01 -> positive match
      /// - 10 -> negative match
      /// - 11 -> both positive and negative match
      /// Since we only need 2 bits, 4 values fit in one byte
      /// The interest value for i is therefore
      /// state[i / 4] & (0b11 << (2 * (i % 4)))) >> (2 * (i % 4)
      vvector<uint8_t> _iStates;
      vvector<uint8_t> _jStates;

      /// @brief the number literals in L
      unsigned _m;
      /// @brief the number literals in M
      unsigned _n;

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
      /// 0 1 2 2 3 3 3 3 ...
      /// ^ ^ ^   ^       ^
      /// such that we have to free the memory only at the start of the next batch (i.e. at position 0, 1, 2, 4... = 2^k)
      /// It is therefore important to start allocating at 1.
      Match **_allocatedMatches;

      /**
       * Creates a new match set for clauses L of size m and M of size n
       *
       * @param m the length of clause L
       * @param n the length of clause M
       */
      MatchSet(unsigned m, unsigned n);

      /**
       * Frees all the matches allocated by the set
       */
      ~MatchSet();

      /**
       * Resizes the match matrix to the given size and clears the matrix
       * Garantees that the a match can be added at index ( @b m - 1, @b n - 1 )
       *
       * @param m the new length of L
       * @param n the new length of M
       *
       * @warning the allocated matches will remain accessible but will be no longer be reserved. I would therefore be prefereable to not keep the matches after calling this function.
       */
      void resize(unsigned m, unsigned n);

      /**
       * Adds a new match to the set
       * @pre Assumes that the matches fields i and j are set and will not change
       * @pre Assumes that the match was allocated by allocateMatch()
       *
       * @param i the index of the literal in L
       * @param j the index of the literal in M
       * @param polarity the polarity of the match
       * @param var the sat variable associated with the match
       * @return a reference to the new match
       */
      Match* addMatch(unsigned i, unsigned j, bool polarity, subsat::Var var);

      /**
       * Returns the vector of matches for the given literal in L.
       * The vectors should not be modified
       * @param i the index of the literal in L
       * @return the vector of matches for the i-th literal in L
       */
      vvector<Match*>& getIMatches(unsigned i);

      /**
       * Returns true if the i-th literal in L has a positive match in the set
       * @param i the index of the literal in L
       * @return whether L_i has a positive match in the set
       */
      bool hasPositiveMatchI(unsigned i);

      /**
       * Returns true if the i-th literal in L has a negative match in the set
       * @param i the index of the literal in L
       * @return whether L_i has a negative match in the set
       */
      bool hasNegativeMatchI(unsigned i);

      /**
       * Returns the vector of matches for the given literal in M.
       * The vectors should not be modified
       * @param j the index of the literal in M
       * @return the vector of matches for the i-th literal in M
       */
      vvector<Match*>& getJMatches(unsigned j);

      /**
       * Returns true if the j-th literal in M has a positive match in the set
       * @param j the index of the literal in M
       * @return whether M_j has a positive match in the set
       */
      bool hasPositiveMatchJ(unsigned j);

      /**
       * Returns true if the j-th literal in M has a negative match in the set
       * @param j the index of the literal in M
       * @return whether M_j has a negative match in the set
       */
      bool hasNegativeMatchJ(unsigned j);

      /**
       * Returns all the matches in the set
       * @return all the matches in the set
       */
      vvector<Match*> getAllMatches();

      /**
       * Returns the match for a given sat variable
       * @param v the variable
       * @return the match for the variable, or nullptr if no match exists
       */
      Match* getMatchForVar(subsat::Var v);

      /**
       * Clears the match set
       * @warning the allocated matches will remain accessible but will be no longer be reserved. I would therefore be prefereable to not keep the matches after calling this function.
       */
      void clear();

      private :
      /**
       * Returns one Match from the pool of allocated matches
       * or allocates more memory and returns one of the newly allocated matches
       * @return a reserved match
       */
      Match* allocateMatch();
    };

    /* Variables */

    /// @brief the base clause
    Kernel::Clause *_L;
    /// @brief the instance clause
    Kernel::Clause *_M;
    /// @brief the number of literals in the base clause
    unsigned _m;
    /// @brief the number of literals in the instance clause
    unsigned _n;
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
    /**
     * Set up the subsumption problem.
     * @pre _L and _M must be set in the checker
     * @pre the Match set is already filled
     * @return false if no solution is possible and true if there may exist a solution.
     */
    bool cnfForSubsumption();

    /**
     * Set up the subsumption resolution problem.
     * @pre _L and _M must be set in the checker
     * @pre the Match set is already filled
     * @return false if no solution is possible and true if there may exist a solution.
     */
    bool cnfForSubsumptionResolution();

    /**
     * @brief Adds one binding to the SAT solver and the match set
     * @param binder the binder between the literals
     * @param varNumber the variable number of the binder
     * @param i the index of the literal in the base clause
     * @param j the index of the literal in the instance clause
     * @param polarity the polarity of the match
     */
    void addBinding(BindingsManager::Binder *binder, unsigned i, unsigned j, bool polarity);

    /**
     * Sets up the problem and cleans the match set
    */
    void setupProblem(Kernel::Clause* L, Kernel::Clause* M);

    /**
     * Checks whether the literals L_i and M_j are can be unified according to the polarity (false meaning negative and true meaning positive)
     * @return true if the literals can be unified
     */
    bool checkAndAddMatch(Kernel::Literal* L_i, Kernel::Literal* M_j, unsigned i, unsigned j, bool polarity);

    /**
     * Fills the match set and the bindings manager with all the possible positive and negative bindings between the literals of L and M.
     * @return false if no subsumption solution is possible, the number of sat variables allocated otherwise.
     */
    bool fillMatchesS();

    /**
     * Fills the match set and the bindings manager with all the possible positive and negative bindings between the literals of L and M.
     * @return false if no subsumption resolution solution is possible, the number of sat variables allocated otherwise.
     */
    bool fillMatchesSR();

    /**
     * Generates the conclusion clause based on the model provided by the sat solver
     * @pre the match set must fill filled
     * @pre the model must be set by the sat solver
     * @return the conclusion clause
     */
    Kernel::Clause* generateConclusion();


  public:
    CLASS_NAME(SATSubsumption);
    USE_ALLOCATOR(SATSubsumption);

    SATSubsumption();
    ~SATSubsumption();

    ///
    bool checkSubsumption(Kernel::Clause* L, Kernel::Clause* M);

    /**
     * Checks whether a subsumption resolution can occur between the clauses @b L and @b M . If it is possible, returns the conclusion of the resolution, otherwise return NULL.
     *
     * L /\ M => L /\ C where C is the conclusion of the subsumption resolution
     *
     * Subsumption resolution is possible for two clauses (~A V C) and (B V D) if there exists a substition "s" such that
     * s(A V C) \\subseteq (B V D)
     * Where A and B are sigle literals and D becomes the conclusion of the subsumption resolution
     * @example
     * [p(x1, x2) V p(f(x2), x3)] /\ [~p2(f(y1), d) V p2(g(y1), c) V ~p2(f(c), e)]
     * ---------------------------------------------------------------------------
     *                  ~p2(f(y1),d) V p2(g(y1),c)
     * thank's to the substitution S = {x1 -> g(y1), x2 -> c, x3 -> e}
     * @remark Subsumption resolution may not be unique, this method has no garantee on which solution will be generated.
     * @example
     * [p(x) V q(x) V r(x)] /\ [P(c) \/ Q(c) \/ ~R(c) \/ P(d) \/ ~Q(d) \/ R(d)]
     * may have several conclusion.
     */
    Kernel::Clause* checkSubsumptionResolution(Kernel::Clause* L, Kernel::Clause* M);

    /**
     * Clears all the caches.
     */
    void clear();
};

}

#endif /* !SAT_SUBSUMPTION_RESOLUTION_HPP */
