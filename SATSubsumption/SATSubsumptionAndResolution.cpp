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
 * Implements class SATSubsumptionAndResolution.
 */

/**
 * THEORETICAL BACKGROUND
 *
 * The SAT-based subsumption and subsumption resolution inference are defined as follows:
 *
 * ----- Subsumption: -----
 * Let L and M be two clauses considered as multisets. L subsumes M iff there exists a substitution s
 * such that s(L) is a sub-multiset of M.
 * Subsumption can occurs iff the three following conditions are satisfied:
 * 1. Completeness : All literals of L have a substitution to M.
 *    There exists s such that forall l_i in L, s(l_i) in M
 * 2. Multiplicity conservation : For each literal l_i in L, there exists at most one
 *    literal m_j in M such that s(l_i) = m_j.
 * 3. Substitution validity : The substitution s is compatible with all the sub-substitutions.
 *
 * ----- Subsumption Resolution: -----
 * Let L and M be two clauses considered as sets. L and M are said to be the base and instance
 * of a subsumption resolution inference, respectively iif
 *    there exists a substitution s,
 *                 a set of literal L' included in L
 *                 a literal m' in M
 *    such that s(L') = {~m'} and s(L) is a subset of M.
 * Subsumption resolution can occur if the 5 following conditions are satisfied:
 * 1. Existence             : There exists a literal l_i in L and a literal m_j such that
 *    s(l_i) = m_j (m' exists).
 * 2. Uniqueness   : There is only one literal m_j such that there exists a literal l_i in L
 *    such that s(l_i) = ~m_j. (m' is unique)
 * 3. Completeness          : All literals of L must either have a substitution to M - {m'} or {~m'}.
 *    Forall l_i in L, there exists m_j in M such that s(l_i) = m_j or s(l_i) = ~m_j
 * 4. Coherence             : Literals in M cannot be mapped by both positive and negative substitutions.
 *    Forall m_j in M, forall l_i, l_i' != l_i in L, s(l_i) = m_j => s(l_i') != ~m_j
 * 5. Substitution validity : The substitution s is compatible with all the sub-substitutions.
 *
 */

#include "Kernel/Matcher.hpp"
#include "Debug/RuntimeStatistics.hpp"
#include "Util.hpp"
#include <iostream>

#include "SATSubsumption/SATSubsumptionAndResolution.hpp"
#include "SATSubsumptionAndResolution.hpp"

using namespace Indexing;
using namespace Kernel;
using namespace SATSubsumption;
using namespace std;

const unsigned INVALID = std::numeric_limits<unsigned>::max();

/****************************************************************************/
/*               SATSubsumptionAndResolution::MatchSet                      */
/****************************************************************************/

void SATSubsumptionAndResolution::MatchSet::indexMatrix()
{
  if (_matchesByJ.size())
    return;

  ASS_EQ(_matchesByJ.size(), 0)
  ASS_EQ(_indexI.size(), 0)
  ASS_EQ(_indexJ.size(), 0)

  for (Match match : _matchesByI)
    _matchesByJ.push_back(match);

  std::sort(
      _matchesByJ.begin(),
      _matchesByJ.end(),
      [](Match left, Match right) { return left.j < right.j; });

  for (unsigned i = 0, idx = 0; i < _m; i++) {
    _indexI.push_back(idx);
    while (idx < _matchesByI.size() && _matchesByI[idx].i == i)
      idx++;
  }
  _indexI.push_back(_matchesByI.size());

  for (unsigned j = 0, idx = 0; j < _n; j++) {
    _indexJ.push_back(idx);
    while (idx < _matchesByJ.size() && _matchesByJ[idx].j == j)
      idx++;
  }
  _indexJ.push_back(_matchesByJ.size());
}

bool SATSubsumptionAndResolution::MatchSet::hasPositiveMatchJ(unsigned j)
{
  // the wizardry is explained in the header file
  ASS(j < _n)
  return (_jStates[j / 4] & (1 << (2 * (j % 4)))) != 0;
}

bool SATSubsumptionAndResolution::MatchSet::hasNegativeMatchJ(unsigned j)
{
  // the wizardry is explained in the header file
  ASS(j < _n)
  return (_jStates[j / 4] & (2 << (2 * (j % 4)))) != 0;
}

/****************************************************************************/
/*       SATSubsumptionAndResolution::SATSubsumptionAndResolution           */
/****************************************************************************/

void SATSubsumptionAndResolution::loadProblem(Clause *L,
                                              Clause *M)
{
  ASS(L)
  ASS(M)
#if VDEBUG
  // Check that two literals are not the same in L and M
  static DHSet<Literal *> lits;
  lits.reset();
  for (unsigned i = 0; i < L->length(); i++) {
    if (!lits.insert((*L)[i])) {
      ASS(false)
    }
  }
  lits.reset();
  for (unsigned i = 0; i < M->length(); i++) {
    if (!lits.insert((*M)[i])) {
      ASS(false)
    }
  }
#endif

#if PRINT_CLAUSES_SUBS
  cout << "----------------------------------------------" << endl;
  cout << "Setting up problem " << L->toString() << " " << M->toString() << endl;
#endif
  _L = L;
  _M = M;
  _m = L->length();
  _n = M->length();

  _matchSet.clear();
  _matchSet.resize(_m, _n);

  _subsumptionImpossible = false;
  _srImpossible = false;

  _solver.clear();
  _bindingsManager.clear();
} // SATSubsumptionAndResolution::loadProblem

/**
 * @brief Heuristically determine whether it is impossible to find a subsumption
 * between _L and _M.
 *
 * The idea is to check whether the multiset of predicates in _L is a subset of
 * the multiset of predicates in _M. If it is not, then it is impossible to find
 * a subsumption.
 *
 * @note If the number of predicates is high, clearing the multiset is expensive.
 * It might be worth remembering which elements are non zero and clear them manually.
 *
 * @return true if subsumption is impossible, false if we don't know
 */
bool SATSubsumptionAndResolution::pruneSubsumption()
{
  ASS(_L)
  ASS(_M)

  if (_L->length() > _M->length()) {
    // if #(L) > #(M) than it is impossible that s(L) is a sub-multiset of M
    _subsumptionImpossible = true;
    return true;
  }

  // multiset of signed predicates in M
  _headerMultiset.clear();
  _headerMultiset.resize(2 * env.signature->predicates());

  // fill in the multiset of functors in M
  for (unsigned i = 0; i < _M->length(); i++)
    _headerMultiset[(*_M)[i]->header()]++;

  // check if the multiset of functors in L is a subset of the multiset of functors in M
  for (unsigned j = 0; j < _L->length(); j++)
    if (!_headerMultiset[(*_L)[j]->header()]--) {
      _subsumptionImpossible = true;
      return true;
    }

  // WARNING !!!
  // In the implementation, it is assumed that the pruning for subsumption resolution
  // is stronger than the pruning for subsumption. Therefore, if the pruning for subsumption
  // resolution occurs, then subsumption must be pruned as well.
  // The remark is left for whoever wants to change this property, the piece of code in
  // checkSubsumption() using the pruning methods must be changed as well.
  //    _srImpossible = pruneSubsumptionResolution();
  //    _subsumptionImpossible = _srImpossible || pruneSubsumption();
  ASS(!pruneSubsumptionResolution())
  return false;
} // SATSubsumptionAndResolution::pruneSubsumption

/**
 * @brief Heuristically determine whether it is impossible to apply subsumption
 * resolution between _L and _M.
 *
 * The idea is to check whether the set of predicates in _L is a subset of the
 * set of predicates in _M. If it is not, then it is impossible to find a
 * subsumption resolution.
 *
 * @return true if subsumption resolution is impossible, false if we don't know
 */
bool SATSubsumptionAndResolution::pruneSubsumptionResolution()
{
  ASS(_L)
  ASS(_M)

  _functorSet.clear();
  _functorSet.resize(env.signature->predicates());

  for (unsigned i = 0; i < _M->length(); i++)
    _functorSet[(*_M)[i]->functor()] = true;

  for (unsigned j = 0; j < _L->length(); j++)
    if (!_functorSet[(*_L)[j]->functor()])
      return true;

  return false;
} // SATSubsumptionAndResolution::pruneSubsumptionResolution

void SATSubsumptionAndResolution::addBinding(BindingsManager::Binder *binder,
                                             unsigned i,
                                             unsigned j,
                                             bool polarity,
                                             bool isNullary)
{
  ASS(binder || isNullary)
  ASS(i < _m)
  ASS(j < _n)
  ASS_EQ((*_L)[i]->functor(), (*_M)[j]->functor())
  ASS_EQ((*_L)[i]->polarity() == (*_M)[j]->polarity(), polarity)
  subsat::Var satVar = _solver.new_variable();
#if PRINT_CLAUSES_SUBS
  cout << satVar << " -> (" << (*_L)[i]->toString() << " " << (*_M)[j]->toString() << " " << (polarity ? "+" : "-") << ")" << endl;
#endif
  _matchSet.addMatch(i, j, polarity, satVar);
  if (!isNullary)
    _bindingsManager.commit_bindings(*binder, satVar, i, j);
} // SATSubsumptionAndResolution::addBinding

#if CORRELATE_LENGTH_TIME
double SATSubsumption::SATSubsumptionAndResolution::getSparsity()
{
  return (double)_matchSet._matchesByI.size() / (double)(_n * _m);
}
#endif

bool SATSubsumptionAndResolution::checkAndAddMatch(Literal *l_i,
                                                   Literal *m_j,
                                                   unsigned i,
                                                   unsigned j,
                                                   bool polarity)
{
  ASS(l_i)
  ASS(m_j)
  ASS_EQ((*_L)[i], l_i)
  ASS_EQ((*_M)[j], m_j)
  ASS_EQ(l_i->functor(), m_j->functor())
  ASS_EQ(l_i->polarity() == m_j->polarity(), polarity)

  bool match = false;
  {
    auto binder = _bindingsManager.start_binder();
    if (MatchingUtils::matchArgs(l_i, m_j, binder)) {
      addBinding(&binder, i, j, polarity, false);
      match = true;
    }
  }
  if (l_i->commutative()) {
    auto binder = _bindingsManager.start_binder();
    if (MatchingUtils::matchReversedArgs(l_i, m_j, binder)) {
      addBinding(&binder, i, j, polarity, false);
      match = true;
    }
  }
  return match;
} // SATSubsumptionAndResolution::checkAndAddMatch

bool SATSubsumptionAndResolution::fillMatchesS()
{
  ASS(_L)
  ASS(_M)
  ASS(_m > 0)
  ASS(_n > 0)
  ASS(_matchSet._m == _m)
  ASS(_matchSet._n == _n)

  Literal *l_i, *m_j;

  // number of matches found is equal to the number of variables in the SAT solver
  for (unsigned i = 0; i < _m; ++i) {
    l_i = _L->literals()[i];
    bool foundMatch = false;

    for (unsigned j = 0; j < _n; ++j) {
      m_j = _M->literals()[j];
      if (l_i->functor() != m_j->functor() || l_i->polarity() != m_j->polarity()) {
        continue;
      }
      if (l_i->arity() == 0) {
        ASS(m_j->arity() == 0)
        ASS(l_i->functor() == m_j->functor())
        addBinding(nullptr, i, j, true, true);
        foundMatch = true;
        continue;
      }
      // it is important that foundMatch is "or-ed" after calling the function. Otherwise the function might not be called.
      // foundMatch |= checkAndAddMatch(l_i, m_j, i, j, true); is NOT correct.
      foundMatch = checkAndAddMatch(l_i, m_j, i, j, true) || foundMatch;
    } // for (unsigned j = 0; j < _n; ++j)

    if (!foundMatch) {
      _subsumptionImpossible = true;
      return false;
    } // if (!foundPositiveMatch)
  }   // for (unsigned i = 0; i < _m; ++i)

  return true;
} // SATSubsumptionAndResolution::fillMatchesS()

void SATSubsumptionAndResolution::fillMatchesSR()
{
  ASS(_L)
  ASS(_M)
  ASS(_m > 0)
  ASS(_n > 0)
  ASS(_matchSet._m == _m)
  ASS(_matchSet._n == _n)

  // stores whether on all the literals in L there is a negative match in M
  bool clauseHasNegativeMatch = false;

  // the first literal in L that only has a negative match (no positive)
  Literal *firstOnlyNegativeMatch = nullptr;

  for (unsigned i = 0; i < _m; ++i) {
    Literal *l_i = _L->literals()[i];

    // does l_i have a positive match in M?
    bool literalHasPositiveMatch = false;
    // does l_i have a negative match in M?
    bool literalHasNegativeMatch = false;

    for (unsigned j = 0; j < _n; ++j) {
      Literal *m_j = _M->literals()[j];
      if (l_i->functor() != m_j->functor())
        continue;
      if (l_i->arity() == 0) {
        ASS(m_j->arity() == 0)
        ASS(l_i->functor() == m_j->functor())
        if (l_i->polarity() == m_j->polarity()) {
          addBinding(nullptr, i, j, true, true);
          literalHasPositiveMatch = true;
          continue;
        }
        addBinding(nullptr, i, j, false, true);
        clauseHasNegativeMatch = true;
        literalHasNegativeMatch = true;
        continue;
      }

      if (l_i->polarity() == m_j->polarity()) {
        // it is important that foundPositiveMatch is "or-ed" after calling the function. Otherwise the function might not be called.
        // foundPositiveMatch |= checkAndAddMatch(l_i, m_j, i, j, true); is NOT correct.
        literalHasPositiveMatch = checkAndAddMatch(l_i, m_j, i, j, true) || literalHasPositiveMatch;
        continue;
      }
      // check negative polarity matches
      // same comment as above
      literalHasNegativeMatch = checkAndAddMatch(l_i, m_j, i, j, false) || literalHasNegativeMatch;
      clauseHasNegativeMatch |= literalHasNegativeMatch;
    } // for (unsigned j = 0; j < _nInstanceLits; ++j)

    // Check whether subsumption and subsumption resolution are possible
    if (!literalHasPositiveMatch) {
      _subsumptionImpossible = true;
      if (!literalHasNegativeMatch) {
        // no positive nor negative matches found
        _srImpossible = true;
        return;
      }
      // TODO try matching?
      if (!firstOnlyNegativeMatch)
        firstOnlyNegativeMatch = l_i;
      else if (firstOnlyNegativeMatch->header() != l_i->header()) {
        // there are two literals in L with only negative polarity matches, but they have a different functor
        // therefore, subsumption resolution is impossible
        _srImpossible = true;
        return;
      }
    } // if (!foundPositiveMatch)
  }   // for (unsigned i = 0; i < _nBaseLits; ++i)

  // If there are no negative matches, then the SR is not possible
  if (!clauseHasNegativeMatch)
    _srImpossible = true;

} // SATSubsumptionAndResolution::fillMatchesSR()

bool SATSubsumptionAndResolution::cnfForSubsumption()
{
  ASS(_L)
  ASS(_M)
  ASS_GE(_matchSet.allMatches().size(), _L->length())
  ASS_G(_L->length(), 0)
  ASS(!_subsumptionImpossible)

  _matchSet.indexMatrix();

  Solver &solver = _solver;

  /**** Completeness ****/
  // Build clauses stating that l_i must be matched to at least one corresponding m_j.
  for (unsigned i = 0; i < _m; ++i) {
    solver.constraint_start();
    for (Match match : _matchSet.getIMatches(i)) {
      if (match.polarity) {
        solver.constraint_push_literal(match.var);
      }
    }
    auto handle = solver.constraint_end();
    solver.add_clause_unsafe(handle);
  }

  /**** Multiplicity conservation ****/
  // Here we store the AtMostOne constraints saying that each instance literal may be matched at most once.
  // Each instance literal can be matched by at most 2 boolean vars per base literal (two orientations of equalities).
  // NOTE: instance constraints cannot be packed densely because we only know their shape at the end.
  // uint32_t const instance_constraint_maxsize = 2 * base_len;
  for (unsigned j = 0; j < _n; ++j) {
    solver.constraint_start();
    for (Match match : _matchSet.getJMatches(j)) {
      if (match.polarity) {
        solver.constraint_push_literal(match.var);
      }
    }
    auto handle = solver.constraint_end();
    solver.add_atmostone_constraint_unsafe(handle);
  }

  return !solver.inconsistent();
} // SATSubsumptionAndResolution::cnfForSubsumption()

SATSubsumptionAndResolution::EncodingMethod SATSubsumption::SATSubsumptionAndResolution::chooseEncoding()
{
  if (forceDirectEncoding)
    return DIRECT;
  if (forceIndirectEncoding)
    return INDIRECT;
  if (_L->length() <= 3)
    return DIRECT;
  return INDIRECT;
}

/**
 * Direct encoding of the sat subsumption resolution
 *
 * @pre assumes that base and instance literals are set, the match set is empty and the solver is empty
 *
 * Let the base clause be L and the instance clause be M.
 *  - We name the literals in L as L1, L2, ..., Ln
 *  - We name the literals in M as M1, M2, ..., Mk
 *
 * We introduce the variables
 *  - b_ij+ if l_i has a substitution s such that s(l_i) = m_j
 *    we will say that b_ij+ as a positive polarity
 *  - b_ij- if l_i has a substitution s such that s(l_i) = ~m_j
 *    we will say that b_ij- as a negative polarity
 * b_ij+ and b_ij- are mutually existentially exclusive, therefore, we only introduce one variable b_ij for the sat solver, and remember its polarity.
 * It may be that both b_ij+ and b_ij- do not exist.
 *
 *
 * We introduce the following subsumption resolution clauses clauses:
 *  - Existence
 *    At least one negative polarity match exists
 *      b_11- V ... V b_1m- V ... V b_n1 V ... V b_nm-
 *  - Uniqueness
 *    At most one m_j is matched by a negative polarity variable
 *      for each j : b_1j- V ... V b_nj- => ~b_ij', j' != j
 *  - Completeness
 *    Each l_i is matched by at least one m_j
 *        b_11 V ... V b_1k /\ b_21 V ... V b_2k
 *     /\ ...
 *     /\ b_n1 V ... V b_nk
 *  - Coherence
 *      for each j, forall i, forall i', ~b_ij+ V ~b_ij'-
 *
 *  - Substitution validity
 *    b_ij implies a certain substitution is valid
 *      for each i, j : b_ij => (s(l_i) = m_j V s(l_i) = ~m_j)
 *    (This rule is enforced by the match set)
 *
 */
bool SATSubsumptionAndResolution::directEncodingForSubsumptionResolution()
{
  ASS(_L)
  ASS(_M)
  ASS_GE(_matchSet.allMatches().size(), _L->length())

  _matchSet.indexMatrix();

  Solver &solver = _solver;

/**** Existence ****/
#if PRINT_CLAUSE_COMMENTS_SUBS
  cout << "Existence" << endl;
#endif
#if PRINT_CLAUSES_SUBS
  vstring s = "";
#endif
  const vvector<Match> &allMatches = _matchSet.allMatches();
  solver.constraint_start();
  for (Match match : allMatches) {
    if (!match.polarity) {
      solver.constraint_push_literal(match.var);
#if PRINT_CLAUSES_SUBS
      s += Int::toString(match.var.index()) + " V ";
#endif
    }
  }
#if PRINT_CLAUSES_SUBS
  cout << s.substr(0, s.size() - 3) << endl;
#endif
  auto build = solver.constraint_end();
  solver.add_clause_unsafe(build);

/**** Uniqueness ****/
#if PRINT_CLAUSE_COMMENTS_SUBS
  cout << "Uniqueness" << endl;
#endif
  for (unsigned it1 = 0; it1 < allMatches.size(); it1++) {
    Match match1 = allMatches[it1];
    if (match1.polarity) {
      continue;
    }
    for (unsigned it2 = it1 + 1; it2 < allMatches.size(); it2++) {
      Match match2 = allMatches[it2];
      if (match2.polarity || match1.j == match2.j) {
        continue;
      }
      solver.constraint_start();
      solver.constraint_push_literal(~match1.var);
      solver.constraint_push_literal(~match2.var);
      auto build = solver.constraint_end();
      solver.add_clause_unsafe(build);
#if PRINT_CLAUSES_SUBS
      cout << ~match1.var << " V " << ~match2.var << endl;
#endif
    }
  }

/**** Completeness ****/
#if PRINT_CLAUSE_COMMENTS_SUBS
  cout << "Completeness" << endl;
#endif
  for (unsigned i = 0; i < _m; i++) {
    solver.constraint_start();
#if PRINT_CLAUSES_SUBS
    s = "";
#endif
    for (Match match : _matchSet.getIMatches(i)) {
      solver.constraint_push_literal(match.var);
#if PRINT_CLAUSES_SUBS
      s += Int::toString(match.var.index()) + " V ";
#endif
    }
#if PRINT_CLAUSES_SUBS
    cout << s.substr(0, s.size() - 3) << endl;
#endif
    auto build = solver.constraint_end();
    solver.add_clause_unsafe(build);
  }

/**** Coherence ****/
#if PRINT_CLAUSE_COMMENTS_SUBS
  cout << "Coherence" << endl;
#endif
  for (unsigned j = 0; j < _n; j++) {
    Slice<Match> matches = _matchSet.getJMatches(j);
    for (unsigned i1 = 0; i1 < matches.size(); i1++) {
      Match match1 = matches[i1];
      for (unsigned i2 = i1 + 1; i2 < matches.size(); i2++) {
        Match match2 = matches[i2];
        if (match2.polarity == match1.polarity) {
          continue;
        }
        solver.constraint_start();
        solver.constraint_push_literal(~match1.var);
        solver.constraint_push_literal(~match2.var);
        auto build = solver.constraint_end();
        solver.add_clause_unsafe(build);
#if PRINT_CLAUSES_SUBS
        cout << ~match1.var << " V " << ~match2.var << endl;
#endif
      }
    }
  }
  return !solver.inconsistent();
}

/// @brief a vector used to store the sat variables that are subjected to the at most one constraint (will hold the c_j)
/// The unsigned value is the index of the literal in the instance clause
static vvector<pair<unsigned, subsat::Var>> atMostOneVars;
/**
 * Indirect encoding of the sat subsumption resolution
 *
 * Let the base clause be L and the instance clause be M.
 *  - We name the literals in L as L1, L2, ..., Ln
 *  - We name the literals in M as M1, M2, ..., Mk
 *
 * We introduce the variables
 *  - b_ij+ if l_i has a substitution s such that s(l_i) = m_j
 *    we will say that b_ij+ as a positive polarity
 *  - b_ij- if l_i has a substitution s such that s(l_i) = ~m_j
 *    we will say that b_ij- as a negative polarity
 *  - c_j if m_j is matched by at least one negative polarity variable b_ij-
 * b_ij+ and b_ij- are mutually existentially exclusive, therefore, we only introduce one variable b_ij for the sat solver, and remember its polarity.
 * It may be that both b_ij+ and b_ij- do not exist.
 *
 *
 * We introduce the following subsumption resolution clauses clauses:
 *  - Encoding of c_j
 *    c_j is true iff m_j is matched by at least one negative polarity variable b_ij-
 *    for each j : c_j <=> b_ij- for some i
 *      for each j :(~c_j V b_1j V ... V b_nj)
 *               /\ (c_j V ~b_1j) /\ ... /\ (c_j V ~bnj)
 *  - Existence
 *      c_1 V c_2 V ... V c_n
 *  - Uniqueness
 *      (~c_1 V ~c_2) /\ (~c_1 V ~c_3) /\ ... /\ (~c_2 V ~c_3) /\ ...
 *  - Completeness
 *      b_11 V ... V b_1k /\ b_21 V ... V b_2k /\ ... /\ b_n1 V ... V b_nk
 *  - Coherence
 *    if c_j is true, then there is no positive polarity match b_ij+
 *      for each i,j : (~c_j V ~b_ij+)
 *  - Substitution validity
 *    b_ij implies a certain substitution is valid
 *      for each i, j : b_ij => (s(l_i) = m_j V s(l_i) = ~m_j)
 *    (This rule is enforced by the match set)
 *
 */
bool SATSubsumptionAndResolution::indirectEncodingForSubsumptionResolution()
{
  ASS(_L)
  ASS(_M)
  // This should be pruned when filling the match set.
  ASS_GE(_matchSet.allMatches().size(), _L->length())

  atMostOneVars.clear();
  _matchSet.indexMatrix();
  Solver &solver = _solver;

  /**** Existence ****/
#if PRINT_CLAUSES_SUBS
  vstring s = "";
#endif
  solver.constraint_start();
  for (unsigned j = 0; j < _n; ++j) {
    // Do not add useless variables in the solver
    // It would compromise correctness since a c_j without binding could be true and satisfy c_1 V ... V c_n without making any other clause false.
    if (_matchSet.hasNegativeMatchJ(j)) {
      subsat::Var c_j = solver.new_variable();
      atMostOneVars.push_back(make_pair(j, c_j));
      solver.constraint_push_literal(c_j);
#if PRINT_CLAUSES_SUBS
      s += Int::toString(c_j.index()) + " V ";
#endif
    }
  }
  ASS(!atMostOneVars.empty())
  auto build = solver.constraint_end();
  solver.add_clause_unsafe(build);
#if PRINT_CLAUSES_SUBS
  cout << s.substr(0, s.size() - 3) << endl
       << endl;
#endif

  /**** Uniqueness ****/
  solver.constraint_start();
  for (auto var : atMostOneVars) {
    solver.constraint_push_literal(var.second);
  }
  build = solver.constraint_end();
  solver.add_atmostone_constraint(build);

  /**** Completeness ****/
  for (unsigned i = 0; i < _m; ++i) {
    solver.constraint_start();
    Slice<Match> matches = _matchSet.getIMatches(i);
    for (Match match : matches) {
#if PRINT_CLAUSES_SUBS
      cout << match.var;
      if (match != matches.back()) {
        cout << " V ";
      }
#endif
      solver.constraint_push_literal(match.var);
    }
    auto build = solver.constraint_end();
    solver.add_clause_unsafe(build);
#if PRINT_CLAUSES_SUBS
    cout << endl;
#endif
  }

  /**** Coherence ****/
  for (auto var : atMostOneVars) {
    unsigned j = var.first;
    subsat::Var c_j = var.second;
    if (_matchSet.hasPositiveMatchJ(j)) {
      for (Match match : _matchSet.getJMatches(j)) {
        if (match.polarity) {
          subsat::Var b_ij = match.var;
          solver.constraint_start();
          solver.constraint_push_literal(~c_j);
          solver.constraint_push_literal(~b_ij);
          build = solver.constraint_end();
          solver.add_clause_unsafe(build);
#if PRINT_CLAUSES_SUBS
          cout << ~c_j << " V " << ~b_ij << endl;
#endif
        }
      }
    }
  }

  /**** Encoding of c_j ****/
  // -> c_j is true if and only if there is a negative polarity match b_ij-
  //    for each j : c_j <=> b_ij- for some i
  //    for each j :(~c_j V b_1j- V ... V b_nj-)
  //            /\ (c_j V ~b_1j-) /\ ... /\ (c_j V ~b_nj-)
  for (auto &pair : atMostOneVars) {
    unsigned j = pair.first;
    Slice<Match> matches = _matchSet.getJMatches(j);
    subsat::Var c_j = pair.second;
    solver.constraint_start();
    //   (~c_j V b_1j- V ... V b_nj-)
    solver.constraint_push_literal(~c_j);
#if PRINT_CLAUSES_SUBS
    cout << c_j;
#endif
    for (Match match : matches) {
      if (!match.polarity) {
        solver.constraint_push_literal(match.var);
#if PRINT_CLAUSES_SUBS
        cout << " V " << match.var;
#endif
      }
    } // for (Match match : matches)
#if PRINT_CLAUSES_SUBS
    cout << endl;
#endif
    auto build = solver.constraint_end();
    solver.add_clause_unsafe(build);
    //   (c_j V ~b_1j-) /\ ... /\ (c_j V ~b_nj-)
    for (Match match : matches) {
      if (!match.polarity) {
        solver.constraint_start();
        solver.constraint_push_literal(c_j);
        solver.constraint_push_literal(~match.var);
        auto build = solver.constraint_end();
        solver.add_clause_unsafe(build);
#if PRINT_CLAUSES_SUBS
        cout << c_j << " V " << ~match.var << endl;
#endif
      }
    } // for (Match match : matches)
  }   // for (auto &pair : atMostOneVars)
  return !solver.inconsistent();
} // cnfForSubsumptionResolution

Clause *SATSubsumptionAndResolution::getSubsumptionResolutionConclusion(Clause *M,
                                                                        Literal *m_j,
                                                                        Clause *L)
{
  int mlen = M->length();
  int nlen = mlen - 1;

  Clause *res = new (nlen) Clause(nlen,
                                  SimplifyingInference2(InferenceRule::SUBSUMPTION_RESOLUTION, M, L));

  int next = 0;
  for (int i = 0; i < mlen; i++) {
    Literal *curr = (*M)[i];
    if (curr == m_j)
      continue;
    (*res)[next++] = curr;
  }
  ASS_EQ(next, nlen)
  return res;
}

Clause *SATSubsumptionAndResolution::generateConclusion()
{
  ASS(_L)
  ASS(_M)
  ASS(_m > 0)
  ASS(_n > 0)
  ASS_EQ(_matchSet._m, _m)
  ASS_EQ(_matchSet._n, _n)
  ASS(_model.size() > 0)
  ASS_GE(_matchSet.allMatches().size(), _L->length())

// Provided the solution of the sat solver, we can create the conclusion clause
#if VDEBUG
  unsigned j = INVALID;
  // Check that there is only one negative polarity match to j inside the model
  for (subsat::Lit lit : _model) {
    if (lit.is_positive()) {
      // matches can be null if the variable is a c_j
      if (_matchSet.isMatchVar(lit.var())) {
        Match match = _matchSet.getMatchForVar(lit.var());
        if (!match.polarity) {
          if (j == INVALID) {
            j = match.j;
          }
          else {
            ASS(j == match.j)
          }
        }
      }
    }
  }
#endif
  unsigned toRemove = INVALID;
// find the negative polarity match to j inside the model
#if PRINT_CLAUSES_SUBS
  cout << "Model: ";
  for (subsat::Lit lit : _model) {
    cout << lit << " ";
  }
  cout << endl;
#endif
  for (subsat::Lit lit : _model) {
    if (lit.is_positive()) {
      // matches can be null if the variable is a c_j
      if (_matchSet.isMatchVar(lit.var())) {
        Match match = _matchSet.getMatchForVar(lit.var());
        if (!match.polarity) {
          toRemove = match.j;
          break;
        }
      }
    }
  }
  ASS_EQ(_n, _M->size())
  ASS(toRemove != INVALID)
  return SATSubsumptionAndResolution::getSubsumptionResolutionConclusion(_M, (*_M)[toRemove], _L);
} // SATSubsumptionResolution::generateConclusion

bool SATSubsumptionAndResolution::checkSubsumption(Clause *L,
                                                   Clause *M,
                                                   bool setSR)
{
  bool result = checkSubsumptionImpl(L, M, setSR);
#if LOG_SSR_CLAUSES
  _logger->logSubsumption(L, M, result);
#endif
  return result;
}

bool SATSubsumptionAndResolution::checkSubsumptionImpl(Clause *L,
                                                       Clause *M,
                                                       bool setSR)
{
  ASS(L)
  ASS(M)

  loadProblem(L, M);

  // Fill the matches
  if (setSR) {
    _srImpossible = pruneSubsumptionResolution();
    // WARNING!!! This assumes that the check for subsumption resolution is stronger than
    // the check for subsumption.
    _subsumptionImpossible = _srImpossible || pruneSubsumption();

    if (_srImpossible && _subsumptionImpossible)
      return false;
    else {
      ASS(!_srImpossible)
      fillMatchesSR();
    }
    if (_subsumptionImpossible) {
      return false;
    }
  } // if (setSR)
  else if (pruneSubsumption() || !fillMatchesS()) {
    return false;
  }

  ASS_GE(_matchSet.allMatches().size(), _L->length())

#if CORRELATE_LENGTH_TIME
  start = chrono::high_resolution_clock::now();
#endif

  // Create the constraints for the sat solver
  if (!cnfForSubsumption()) {
#if CORRELATE_LENGTH_TIME
    stop = chrono::high_resolution_clock::now();
    auto duration = stop - start;
    if (log) {
      logFile << 0 /* S */ << ","
              << _L->length() << ","
              << _M->length() << ","
              // << getSparsity() << ","
              << duration.count() << ","
              << 0 /* result */ << ","
              << 0 /* no SAT call */ << ","
              << 0 /* SAT ticks */ << ",";
              // << 0 /* SAT conflicts */ << ","
              // << 0 /* SAT decisions */ << ","
              // << 0 /* SAT propagations */ << ","
              // << 0 /* SAT max storage */ << ","
              // << 0 /* SAT original clauses */ << ","
              // << 0 /* SAT original AMOs */ << "\n";
    }
#endif
    return false;
  }

  // Solve the SAT problem
  _solver.theory().setBindings(&_bindingsManager);
  bool const subsumed = _solver.solve() == subsat::Result::Sat;

#if CORRELATE_LENGTH_TIME
  stop = chrono::high_resolution_clock::now();
  auto duration = stop - start;
  if (log) {
    logFile << 0 /* S */ << ","
            << _L->length() << ","
            << _M->length() << ","
            // << getSparsity() << ","
            << duration.count() << ","
            << subsumed /* result */ << ","
            << 1 /* SAT call */ << ","
            << _solver.stats().ticks << ",";
            // << _solver.stats().conflicts /* SAT conflicts */ << ","
            // << _solver.stats().decisions /* SAT decisions */ << ","
            // << _solver.stats().propagations /* SAT propagations */ << ","
            // << _solver.stats().max_stored_literals /* SAT max storage */ << ","
            // << _solver.stats().original_clauses /* SAT original clauses */ << ","
            // << _solver.stats().original_amos /* SAT original AMOs */ << "\n";
  }
#endif
  return subsumed;
} // SATSubsumptionAndResolution::checkSubsumption

Clause *SATSubsumptionAndResolution::checkSubsumptionResolution(Clause *L,
                                                                Clause *M,
                                                                bool usePreviousSetUp)
{
  Clause* result = checkSubsumptionResolutionImpl(L, M, usePreviousSetUp);
#if LOG_SSR_CLAUSES
  _logger->logSubsumptionResolution(L, M, result);
#endif
  return result;
}

Clause *SATSubsumptionAndResolution::checkSubsumptionResolutionImpl(Clause *L,
                                                                    Clause *M,
                                                                    bool usePreviousSetUp)
{
  ASS(L)
  ASS(M)
  if (usePreviousSetUp) {
    ASS(_L == L)
    ASS(_M == M)
    if (_srImpossible) {
#if PRINT_CLAUSES_SUBS
      cout << "SR impossible" << endl;
#endif
      return nullptr;
    }
    ASS_GE(_matchSet.allMatches().size(), _L->length())
    // do not clear the variables and bindings
    _solver.clear_constraints();
  }
  else {
    loadProblem(L, M);
    if (pruneSubsumptionResolution()) {
#if PRINT_CLAUSES_SUBS
      cout << "SR pruned" << endl;
#endif
      return nullptr;
    }
    fillMatchesSR();
    if (_srImpossible) {
#if PRINT_CLAUSES_SUBS
      cout << "SR impossible" << endl;
#endif
      return nullptr;
    }
  }

#if CORRELATE_LENGTH_TIME
  start = chrono::high_resolution_clock::now();
#endif
  // set up the clauses
  bool encodingSuccess;
  switch (chooseEncoding()) {
    case EncodingMethod::DIRECT:
      encodingSuccess = directEncodingForSubsumptionResolution();
      break;
    case EncodingMethod::INDIRECT:
      encodingSuccess = indirectEncodingForSubsumptionResolution();
      break;
    default:
      ASS(false);
  }

  if (!encodingSuccess) {
#if PRINT_CLAUSES_SUBS
    cout << "CNF building failed" << endl;
#endif
#if CORRELATE_LENGTH_TIME
    stop = chrono::high_resolution_clock::now();
    auto duration = stop - start;
    if (log) {
      logFile << 1 /* SR */ << ","
              << _L->length() << ","
              << _M->length() << ","
              // << getSparsity() << ","
              << duration.count() << ","
              << 0 /* result */ << ","
              << 0 /* no SAT call */ << ","
              << 0 /* SAT ticks */ << ",";
              // << 0 /* SAT conflicts */ << ","
              // << 0 /* SAT decisions */ << ","
              // << 0 /* SAT propagations */ << ","
              // << 0 /* SAT max storage */ << ","
              // << 0 /* SAT original clauses */ << ","
              // << 0 /* SAT original AMOs */ << "\n";
    }
#endif
    return nullptr;
  }

  // Solve the SAT problem
  if (_solver.theory().empty()) {
    // -> b_ij implies a certain substitution is valid
    //    for each i, j : b_ij => (S(l_i) = m_j V S(l_i) = ~m_j)
    // These constraints are created in the fillMatches() function by filling the _bindingsManager
    _solver.theory().setBindings(&_bindingsManager);
  }
  Clause *conclusion = nullptr;
  if (_solver.solve() == subsat::Result::Sat) {
#if PRINT_CLAUSES_SUBS
    cout << "SAT solver succeeded" << endl;
#endif
    _model.clear();
    _solver.get_model(_model);
    conclusion = generateConclusion();
  }
#if PRINT_CLAUSES_SUBS
  else {
    cout << "SAT solver failed" << endl;
  }
#endif

#if CORRELATE_LENGTH_TIME
  stop = chrono::high_resolution_clock::now();
  auto duration = stop - start;
  if (log) {
    logFile << 1 /* SR */ << ","
            << _L->length() << ","
            << _M->length() << ","
            // << getSparsity() << ","
            << duration.count() << ","
            << !!conclusion /* result */ << ","
            << 1 /* SAT call */ << ","
            << _solver.stats().ticks << ",";
            // << _solver.stats().conflicts /* SAT conflicts */ << ","
            // << _solver.stats().decisions /* SAT decisions */ << ","
            // << _solver.stats().propagations /* SAT propagations */ << ","
            // << _solver.stats().max_stored_literals /* SAT max storage */ << ","
            // << _solver.stats().original_clauses /* SAT original clauses */ << ","
            // << _solver.stats().original_amos /* SAT original AMOs */ << "\n";
  }
#endif
  // If the problem is SAT, then generate the conclusion clause
  return conclusion;
} // SATSubsumptionAndResolution::checkSubsumptionResolution
