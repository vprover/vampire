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
 * @file SATSubsumptionAndResolution.cpp
 * Defines class SATSubsumptionAndResolution.
 */
#ifndef SAT_SUBSUMPTION_RESOLUTION_HPP
#define SAT_SUBSUMPTION_RESOLUTION_HPP

#include "Kernel/Clause.hpp"
#include "Lib/STL.hpp"
#include "./subsat/subsat.hpp"

#include "SATSubsumption/SATSubsumptionConfig.hpp"

#if WRITE_LITERAL_MATCHES_FILE
#include <iostream> //include the header files like input-output streams
#include <fstream>  //include the filestreamobject as the header files
#endif

namespace SATSubsumption {
class SATSubsumptionAndResolution;

/**
 * Class implementing the simplifying rules of subsumption and subsumption resolution using
 * a SAT solver.
 */
class SATSubsumptionAndResolution {
#if VDEBUG
// Make it public to allow unit testing
public:
#else
private:
#endif
  template <typename T>
  using allocator_type = STLAllocator<T>;
  using Solver = subsat::Solver<allocator_type>;
  using BindingsManager = typename Solver::BindingsManager;

  // just to satisfy Vampire's custom allocator
  struct SolverWrapper {
    CLASS_NAME(SATSubsumptionAndResolution::SolverWrapper);
    USE_ALLOCATOR(SATSubsumptionAndResolution::SolverWrapper);
    Solver s;
  };

  /**
   * A Match represents a binding between two literals l_i and m_j of different clauses L and M.
   * The binding can be either positive or negative
   */
  struct Match {
    CLASS_NAME(SATSubsumptionAndResolution::Match);

    // The index of the literal in L (base clause for subsumption resolution)
    unsigned _i;
    // The index of the literal in M (instance clause for subsumption resolution)
    unsigned _j;
    // The polarity of the match (true for positive, false for negative)
    bool _polarity;
    // The variable associated in the sat solver
    subsat::Var _var;

    Match() : _i(0),
              _j(0),
              _polarity(true),
              _var(subsat::Var(0)) {}

    Match(unsigned baseLitIndex,
          unsigned instanceLitIndex,
          bool isPositive,
          subsat::Var satVar) : _i(baseLitIndex),
                                _j(instanceLitIndex),
                                _polarity(isPositive),
                                _var(satVar) {}

    std::string toString() const
    {
      return "Match(" + to_string(_i) + ", " + to_string(_j) + ", " + to_string(_polarity) + ", " + to_string(_var.index()) + ")";
    }

    bool operator==(const Match &other) const
    {
      return _i == other._i && _j == other._j && _polarity == other._polarity && _var == other._var;
    }

    bool operator!=(const Match &other) const
    {
      return !(*this == other);
    }
  };

  /**
   * A Match set is a facility to store matches, and allows to enumerate them either according to the clause L or M indices.
   * The Match Set, when filled contains all the bindings possible between the clauses L and M
   * The match set can be abstracted as a sparse matrix holding the associated sat variable and polarity of the matches
   *
   * @example For example, here is a table of matches (not necessarily coherent with the subsumption resolution problem)
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
    CLASS_NAME(SATSubsumptionAndResolution::MatchSet);
    USE_ALLOCATOR(SATSubsumptionAndResolution::MatchSet);
    friend struct Match;

    /// @brief Holds the matches grouped by _i
    /// _iMatches[i] holds the list of matches for the i'th literal in L
    /// the list is stored in the order in which they are added to the set
    Lib::vvector<Lib::vvector<Match>> _iMatches;
    /// @brief Holds the matches grouped by _j
    /// _jMatches[j] holds the list of matches for the j'th literal in M
    /// the list is stored in the order in which they are added to the set
    Lib::vvector<Lib::vvector<Match>> _jMatches;

#if SAT_SR_IMPL == 2
    /// @brief Metadata remembering whether some positive match or negative match was found for each literal in M
    /// @remark
    /// This information only needs 2 bits
    /// - 00 -> no match
    /// - 01 -> positive match
    /// - 10 -> negative match
    /// - 11 -> both positive and negative match
    /// Since we only need 2 bits, 4 values fit in one byte
    /// The interest value for i is therefore
    /// state[j / 4] & (0b11 << (2 * (j % 4))) >> (2 * (j % 4))
    /// @example For example, if we have 5 literals in M, the state will be
    /// 0b 00 10 01 11 | 0b 00
    /// and the interest value for j=2 will be state[0]
    /// 0b 00 10 01 11
    /// After passing the mask 0b 00 11 0 00 (= (0b11 << (2 * (2 % 4)))) )
    /// 0b 00 10 00 00
    /// After shifting 4 bits to the right (>> (2 * (j % 4)))
    /// 0b 00 00 00 10
    /// We know that m_2 does not have a positive match, but has a negative match
    Lib::vvector<uint8_t> _jStates;
#endif

    /// @brief the number literals in L
    unsigned _m;
    /// @brief the number literals in M
    unsigned _n;

    /// @brief contains the list of all the the matches indexed in the match set
    /// If the properties of AddMatch are respected, then _matches[i] is the match with the sat variable i
    Lib::vvector<Match> _matches;

    /**
     * Creates a new match set for clauses L of size m and M of size n
     *
     * @param m the length of clause L
     * @param n the length of clause M
     */
    MatchSet(unsigned m,
             unsigned n);

    /**
     * Frees all the matches allocated by the set
     */
    ~MatchSet();

    /**
     * Resizes the match matrix to the given size and clears the matrix
     * Guarantees that the a match can be added at index ( @b m - 1, @b n - 1 )
     *
     * @param m the new length of L
     * @param n the new length of M
     *
     * @warning the allocated matches will remain accessible but will be no longer be reserved. It would therefore be preferable to not keep the matches after calling this function.
     */
    void resize(unsigned m,
                unsigned n);

    /**
     * Adds a new match to the set
     *
     * @pre the match must be valid (i.e. @b i < _m and @b j < _n)
     * @pre the sar variable @b var must follow the one that was added before, or be 0 if no match was added before
     *
     * @param i the index of the literal in L
     * @param j the index of the literal in M
     * @param polarity the polarity of the match
     * @param var the sat variable associated with the match
     * @return the newly added match
     */
    SATSubsumptionAndResolution::Match addMatch(unsigned i,
                                                unsigned j,
                                                bool polarity,
                                                subsat::Var var);

    /**
     * Returns the vector of matches for the given literal in L.
     * The vectors should not be modified
     *
     * @param i the index of the literal in L
     * @return the vector of matches for the i-th literal in L
     */
    Lib::vvector<Match> &getIMatches(unsigned i);

    /**
     * Returns the vector of matches for the given literal in M.
     * The vectors should not be modified
     *
     * @param j the index of the literal in M
     * @return the vector of matches for the j-th literal in M
     */
    Lib::vvector<Match> &getJMatches(unsigned j);

#if SAT_SR_IMPL == 2
    /**
     * Returns true if the j-th literal in M has a positive match in the set
     *
     * @param j the index of the literal in M
     * @return whether m_j has a positive match in the set
     */
    bool hasPositiveMatchJ(unsigned j);

    /**
     * Returns true if the j-th literal in M has a negative match in the set
     *
     * @param j the index of the literal in M
     * @return whether m_j has a negative match in the set
     */
    bool hasNegativeMatchJ(unsigned j);
#endif

    /**
     * Returns all the matches in the set
     *
     * @return all the matches in the set
     */
    Lib::vvector<Match> getAllMatches();

    /**
     * Returns the number of matches in the set
     *
     * @return the number of matches in the set
     */
    unsigned getMatchCount();

    /**
     * Checks whether the sat variable @b v is linked to a match
     *
     * @pre Assumes that the matches are linked to variables in an increasing order
     * (the first match being associated with variable 0, then 1, and so on)
     * No leaps are authorized
     * @param v the variable
     * @return true if the variable is a match variable
     */
    bool isMatchVar(subsat::Var v);

    /**
     * Returns the match for a given sat variable
     *
     * @pre Assumes that the matches are linked to variables in an increasing order
     * (the first match being associated with variable 0, then 1, and so on)
     * No leaps are authorized
     * @param v the variable
     * @return the match for the variable, or nullptr if no match exists
     */
    Match getMatchForVar(subsat::Var v);

    /**
     * Clears the match set
     *
     * @warning the allocated matches will remain accessible but will be no longer be reserved. I would therefore be preferable to not keep the matches after calling this function.
     */
    void clear();
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
  /// @brief the match set used to store the matches between the base and instance clauses
  MatchSet _matchSet;
  /// @brief model of the SAT solver
  Lib::vvector<subsat::Lit> _model;

  // remembers if the fillMatchesSR concluded that subsumption is impossible
  bool _subsumptionImpossible;
  // remembers if the fillMatchesSR concluded that subsumption resolution is impossible
  bool _srImpossible;

  /* Methods */
  /**
   * Sets up the problem and cleans the match set and bindings
   *
   * @param L the base clause
   * @param M the instance clause
   */
  void setupProblem(Kernel::Clause *L,
                    Kernel::Clause *M);

  /**
   * Heuristically predicts whether subsumption or subsumption resolution will fail.
   * This method should be fast.
   *
   * @return true if subsumption is impossible
   */
  bool pruneSubsumption();

  /**
   * Heuristically predicts whether subsumption resolution will fail.
   * This method should be fast
   *
   * @return true if subsumption resolution is impossible
   */
  bool pruneSubsumptionResolution();

  /**
   * Adds one binding to the SAT solver and the match set
   *
   * @param binder the binder between the literals
   * @param varNumber the variable number of the binder
   * @param i the index of the literal in the base clause
   * @param j the index of the literal in the instance clause
   * @param polarity the polarity of the match
   */
  void addBinding(BindingsManager::Binder *binder,
                  unsigned i,
                  unsigned j,
                  bool polarity);

  /**
   * Adds the clauses for the subsumption problem to the sat solver
   *
   * @pre _L and _M must be set in the checker
   * @pre the Match set is already filled
   * @return false if no solution is possible and true if there may exist a solution.
   */
  bool cnfForSubsumption();

  /**
  * Adds the clauses for the subsumption resolution problem to the sat solver
   *
   * @remark The BindingsManager is not required to be set up in this method.
   * @pre _L and _M must be set in the checker
   * @pre the Match set is already filled
   * @return false if no solution is possible and true if there may exist a solution.
   */
  bool cnfForSubsumptionResolution();

  /**
   * Checks whether there exists a substitution from the literals @b l_i and @b m_j.
   * If there exists a substitution, it is added to the match set.
   *
   * @pre Assumes that the polarity and functors of the match was already checked.
   *
   * @param l_i one literal of the base clause
   * @param m_j one literal of the instance clause
   * @param i the index of the literal in the base clause
   * @param j the index of the literal in the instance clause
   * @param polarity the polarity of the match
   * @return true if the literals are matched
   */
  bool checkAndAddMatch(Kernel::Literal *l_i,
                        Kernel::Literal *m_j,
                        unsigned i,
                        unsigned j,
                        bool polarity);

  /**
   * Fills the match set and the bindings manager with all the possible positive bindings between the literals of L and M.
   *
   * @return false if no subsumption solution is possible, the number of sat variables allocated otherwise.
   */
  bool fillMatchesS();

  /**
   * Fills the match set and the bindings manager with all the possible positive and negative bindings between the literals of L and M.
   *
   * @return false if no subsumption resolution solution is possible, the number of sat variables allocated otherwise.
   */
  void fillMatchesSR();

  /**
   * Generates the conclusion clause based on the model provided by the sat solver
   *
   * @pre the match set must fill filled
   * @pre the model must be set by the sat solver
   * @return the conclusion clause
   */
  Kernel::Clause *generateConclusion();

public:
  CLASS_NAME(SATSubsumptionAndResolution);
  USE_ALLOCATOR(SATSubsumptionAndResolution);

  SATSubsumptionAndResolution();
  ~SATSubsumptionAndResolution();

  /**
   * Checks whether the instance clause is subsumed by the base clause
   *
   * @param L the base clause
   * @param M the instance clause
   * @param setNegative if true, the Match set will be filled with negative matches as well.
   * @return true if M is subsumed by L
   *
   * @remark The @b setNegative parameter is used to save time on the setup of subsumption resolution. If it is intended to check for subsumption resolution right after, it is better to set it to true and call checkSubsumptionResolution with the flag usePreviousMatchSet set to true.
   *
   * A clause L subsumes a clause M if there exists a substitution \f$\sigma\f$ such that \f$\sigma(L)\subseteq M\f$.
   * Where L and M are considered as multisets of literals.
   */
  bool checkSubsumption(Kernel::Clause *L,
                        Kernel::Clause *M,
                        bool setNegative = false);

  /**
   * Checks whether a subsumption resolution can occur between the clauses @b L and @b M . If it is possible, returns the conclusion of the resolution, otherwise return NULL.
   *
   * @param L the base clause
   * @param M the instance clause
   * @param usePreviousMatchSet whether to use the previous match set or not. If false, the match set will be cleared and filled again.
   * @return the conclusion of the resolution, or NULL if no resolution is possible
   *
   * @warning if the @b usePreviousMatchSet flag is true, the last call must have been a call to checkSubsumption with the flag setNegative set to true.
   *
   * L /\ M => L /\ M* where M* is the conclusion of the subsumption resolution
   *
   * Subsumption resolution is possible for two clauses (L* V L') and (m' V M*) if there exists a substitution "s" such that
   * s(L') = {~m'} /\ s(L*) \\subseteq M*
   * Where m' is a single literal. The conclusion of the subsumption resolution becomes M*.
   * @example
   * [p(x1, x2) V p(f(x2), x3)] /\ [~p2(f(y1), d) V p2(g(y1), c) V ~p2(f(c), e)]
   * ---------------------------------------------------------------------------
   *                  ~p2(f(y1),d) V p2(g(y1),c)
   * thank's to the substitution S = {x1 -> g(y1), x2 -> c, x3 -> e}
   * @remark Subsumption resolution may not be unique, this method has no guarantee on which solution will be generated.
   * @example
   * [p(x) V q(x) V r(x)] /\ [P(c) \/ Q(c) \/ ~R(c) \/ P(d) \/ ~Q(d) \/ R(d)]
   * may have several conclusion.
   */
  Kernel::Clause *checkSubsumptionResolution(Kernel::Clause *L,
                                             Kernel::Clause *M,
                                             bool usePreviousMatchSet = false);

  /**
   * Creates a clause that is the subsumption resolution of @b M and @b L on @b m_j.
   * L V L' /\ M* V @b m_j => L V L' /\ M*
   *
   * @param M The clause to be subsumed after resolution.
   * @param m_j The literal on which the subsumption resolution is performed.
   * @param L The clause resolving with @b M.
   */
  static Kernel::Clause *getSubsumptionResolutionConclusion(Kernel::Clause *M,
                                                            Kernel::Literal *m_j,
                                                            Kernel::Clause *L);
};

} // namespace SATSubsumption

#endif /* !SAT_SUBSUMPTION_RESOLUTION_HPP */
