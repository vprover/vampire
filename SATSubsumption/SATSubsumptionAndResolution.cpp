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
 * Subsumption can occurs if the three following conditions are satisfied:
 * 1. Completeness : All literals of L have a substitution to M.
 *    There exists s such that forall l_i in L, (l_i) in M
 * 2. Multiplicity conservation : For each literal l_i in L, there exists at most one
 *    literal m_j in M such that s(l_i) = m_j.
 * 3. Substitution validity : The substitution s is compatible with all the substitutions.
 *
 * ----- Subsumption Resolution: -----
 * Let L and M be two clauses considered as sets. L and M are said to be the base and instance
 * of a subsumption resolution inference, respectively iif
 *    there exists a substitution s,
 *                 a set of literal L' included in L
 *                 a literal m' in M
 *    such that s(L') = {~m'} and s(L) is a subset of M.
 * Subsumption resolution can occur if the 5 following conditions are satisfied:
 * 1. Existence    : There exists a literal l_i in L and a literal m_j such that
 *    s(l_i) = m_j (m' exists).
 * 2. Uniqueness   : There is only one literal m_j such that there exists a literal l_i in L
 *    such that s(l_i) = m_j. (m' is unique)
 * 3. Completeness : All literals of L must either have a substitution to M-{m'} or {~m'}.
 *    Forall l_i in L, there exists m_j in M such that s(l_i) = m_j or s(l_i) = ~m_j
 * 4. Coherence    : Literals in M cannot be mapped by both positive and negative substitutions.
 * 5. Substitution validity : The substitution s is compatible with all the substitutions.
 *
 */

#include "Kernel/Matcher.hpp"
#include "Debug/RuntimeStatistics.hpp"
#include "Util.hpp"
#include <iostream>

#include "SATSubsumption/SATSubsumptionAndResolution.hpp"

using namespace Indexing;
using namespace Kernel;
using namespace SATSubsumption;

/****************************************************************************/
/*               SATSubsumptionAndResolution::MatchSet                      */
/****************************************************************************/
SATSubsumptionAndResolution::MatchSet::MatchSet(unsigned m, unsigned n)
    : _iMatches(m),
      _jMatches(n),
#if SAT_SR_IMPL == 2
      _jStates(n / 4 + 1, 0),
#endif
      _m(m),
      _n(n),
      _matches(0)
{
  ASS(m > 0);
  ASS(n > 0);
}

SATSubsumptionAndResolution::MatchSet::~MatchSet()
{
  CALL("SATSubsumptionAndResolution::MatchSet::~MatchSet");
}

SATSubsumptionAndResolution::Match SATSubsumptionAndResolution::MatchSet::addMatch(unsigned i,
                                                                                   unsigned j,
                                                                                   bool polarity,
                                                                                   subsat::Var var)
{
  CALL("SATSubsumptionAndResolution::MatchSet::addMatch")
  ASS(i < _m)
  ASS(j < _n)
  // Make sure that the variables are pushed in order.
  // Otherwise would break the property that _matches[i] is the match associated
  //    to the sat variable i
  ASS_EQ(var.index(), _matches.size())

  Match match(i, j, polarity, var);
  _iMatches[i].push_back(match);
  _jMatches[j].push_back(match);

  _matches.push_back(match);
#if SAT_SR_IMPL == 2
  // update the match state
  // the wizardry is explained in the header file
  if (match._polarity) {
    _jStates[j / 4] |= 1 << (2 * (j % 4));
  }
  else {
    _jStates[j / 4] |= 1 << (2 * (j % 4) + 1);
  }
#endif
  return match;
} // SATSubsumptionAndResolution::MatchSet::addMatch

vvector<SATSubsumptionAndResolution::Match> &SATSubsumptionAndResolution::MatchSet::getIMatches(unsigned i)
{
  ASS(i < _m);
  return _iMatches[i];
}

vvector<SATSubsumptionAndResolution::Match> &SATSubsumptionAndResolution::MatchSet::getJMatches(unsigned j)
{
  ASS(j < _n);
  return _jMatches[j];
}

vvector<SATSubsumptionAndResolution::Match> SATSubsumptionAndResolution::MatchSet::getAllMatches()
{
  return _matches;
}

unsigned SATSubsumptionAndResolution::MatchSet::getMatchCount()
{
  return _matches.size();
}

SATSubsumptionAndResolution::Match SATSubsumptionAndResolution::MatchSet::getMatchForVar(subsat::Var satVar)
{
  CALL("SATSubsumptionAndResolution::MatchSet::getMatchForVar")
  ASS(isMatchVar(satVar))
  return _matches[satVar.index()];
}

bool SATSubsumptionAndResolution::MatchSet::isMatchVar(subsat::Var satVar)
{
  CALL("SATSubsumptionAndResolution::MatchSet::isMatchVar")
  return satVar.index() < _matches.size();
}

#if SAT_SR_IMPL == 2
bool SATSubsumptionAndResolution::MatchSet::hasPositiveMatchJ(unsigned j)
{
  // the wizardry is explained in the header file
  ASS(j < _n);
  return (_jStates[j / 4] & (1 << (2 * (j % 4)))) != 0;
}

bool SATSubsumptionAndResolution::MatchSet::hasNegativeMatchJ(unsigned j)
{
  // the wizardry is explained in the header file
  ASS(j < _n);
  return (_jStates[j / 4] & (2 << (2 * (j % 4)))) != 0;
}
#endif

void SATSubsumptionAndResolution::MatchSet::resize(unsigned newM,
                                                   unsigned newN)
{
  CALL("SATSubsumptionAndResolution::MatchSet::resize");
  ASS(newM > 0)
  ASS(newN > 0)
  _iMatches.resize(newM);
  _jMatches.resize(newN);
  _m = newM;
  _n = newN;
}

void SATSubsumptionAndResolution::MatchSet::clear()
{
  CALL("SATSubsumptionAndResolution::MatchSet::clear");
  for (unsigned i = 0; i < _m; i++) {
    _iMatches[i].clear();
  }
  for (unsigned j = 0; j < _n; j++) {
    _jMatches[j].clear();
  }
  _matches.clear();
}

/****************************************************************************/
/*       SATSubsumptionAndResolution::SATSubsumptionAndResolution           */
/****************************************************************************/
SATSubsumptionAndResolution::SATSubsumptionAndResolution() : _L(nullptr),
                                                             _M(nullptr),
                                                             _m(0),
                                                             _n(0),
                                                             _solver(new SolverWrapper()),
                                                             _bindingsManager(new BindingsManager()),
                                                             _matchSet(1, 1),
                                                             _model(){
                                                                 ASS(_solver)
                                                                     ASS(_bindingsManager)}

                                                             SATSubsumptionAndResolution::~SATSubsumptionAndResolution()
{
  CALL("SATSubsumptionAndResolution::~SATSubsumptionAndResolution");
  delete _solver;
  delete _bindingsManager;
}

void SATSubsumptionAndResolution::setupProblem(Clause *L,
                                               Clause *M)
{
  CALL("SATSubsumptionAndResolution::setupProblem");
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

  _solver->s.clear();
  _bindingsManager->clear();
} // SATSubsumptionAndResolution::setupProblem

/**
 * @brief Heuristically determine whether it is impossible to find a subsumption
 * between _L and _M.
 *
 * The idea is to check whether the multiset of predicates in _L is a subset of
 * the multiset of predicates in _M. If it is not, then it is impossible to find
 * a subsumption.
 *
 * @return true if subsumption is impossible, false if we don't know
 */
bool SATSubsumptionAndResolution::pruneSubsumption()
{
  CALL("SATSubsumptionAndResolution::pruneSubsumption")
  ASS(_L)
  ASS(_M)

  if (_L->length() > _M->length()) {
    // if #(L) > #(M) than it is impossible that s(L) is a sub-multiset of M
    _subsumptionImpossible = true;
    return true;
  }

  // multiset of predicates in M
  static DHMap<pair<unsigned, bool>, unsigned> functors;
  functors.reset();
  // fill in the multiset of functors in M
  for (unsigned i = 0; i < _M->length(); i++) {
    Literal *lit = (*_M)[i];
    auto pair = make_pair(lit->functor(), lit->polarity());
    unsigned *count = functors.findPtr(pair);
    if (count) {
      (*count)++;
    }
    else {
      functors.insert(pair, 1);
    }
  }
  // check if the multiset of functors in L is a subset of the multiset of functors in M
  for (unsigned j = 0; j < _L->length(); j++) {
    Literal *lit = (*_L)[j];
    auto pair = make_pair(lit->functor(), lit->polarity());
    unsigned *count = functors.findPtr(pair);
    if (!count || *count == 0) {
      _subsumptionImpossible = true;
      return true;
    }
    else {
      (*count)--;
    }
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
  CALL("SATSubsumptionAndResolution::pruneSubsumptionResolution")
  ASS(_L)
  ASS(_M)
  static DHSet<unsigned> functors;
  functors.reset();
  for (unsigned i = 0; i < _M->length(); i++) {
    Literal *lit = (*_M)[i];
    functors.insert(lit->functor());
  }
  for (unsigned j = 0; j < _L->length(); j++) {
    Literal *lit = (*_L)[j];
    if (!functors.find(lit->functor())) {
      return true;
    }
  }
  return false;
} // SATSubsumptionAndResolution::pruneSubsumptionResolution

void SATSubsumptionAndResolution::addBinding(BindingsManager::Binder *binder,
                                             unsigned i,
                                             unsigned j,
                                             bool polarity)
{
  CALL("SATSubsumptionAndResolution::addBinding");
  ASS(binder)
  ASS(i < _m)
  ASS(j < _n)
  subsat::Var satVar = _solver->s.new_variable();
#if PRINT_CLAUSES_SUBS
  cout << satVar << " -> (" << (*_L)[i]->toString() << " " << (*_M)[j]->toString() << " " << (polarity ? "+" : "-") << ")" << endl;
#endif
  _matchSet.addMatch(i, j, polarity, satVar);
  _bindingsManager->commit_bindings(*binder, satVar, i, j);
} // SATSubsumptionAndResolution::addBinding

bool SATSubsumptionAndResolution::checkAndAddMatch(Literal *l_i,
                                                   Literal *m_j,
                                                   unsigned i,
                                                   unsigned j,
                                                   bool polarity)
{
  CALL("SATSubsumptionAndResolution::checkAndAddMatch")
  ASS(l_i)
  ASS(m_j)
  ASS_EQ((*_L)[i], l_i)
  ASS_EQ((*_M)[j], m_j)
  ASS_EQ(l_i->functor(), m_j->functor())
  ASS_EQ(l_i->polarity() == m_j->polarity(), polarity)

  bool match = false;
  {
    auto binder = _bindingsManager->start_binder();
    if (MatchingUtils::matchArgs(l_i, m_j, binder)) {
      addBinding(&binder, i, j, polarity);
      match = true;
    }
  }
  if (l_i->commutative()) {
    auto binder = _bindingsManager->start_binder();
    if (MatchingUtils::matchReversedArgs(l_i, m_j, binder)) {
      addBinding(&binder, i, j, polarity);
      match = true;
    }
  }
  return match;
} // SATSubsumptionAndResolution::checkAndAddMatch

bool SATSubsumptionAndResolution::fillMatchesS()
{
  CALL("SATSubsumptionAndResolution::fillMatchesS");
  ASS(_L);
  ASS(_M);
  ASS(_m > 0);
  ASS(_n > 0);
  ASS(_matchSet._m == _m);
  ASS(_matchSet._n == _n);
  ASS(_bindingsManager);

  Literal *l_i, *m_j;

  // number of matches found - is equal to the number of variables in the SAT solver
  for (unsigned i = 0; i < _m; ++i) {
    l_i = _L->literals()[i];
    bool foundMatch = false;

    for (unsigned j = 0; j < _n; ++j) {
      m_j = _M->literals()[j];
      if (l_i->functor() != m_j->functor() || l_i->polarity() != m_j->polarity()) {
        continue;
      }
      foundMatch = checkAndAddMatch(l_i, m_j, i, j, true) || foundMatch;
    } // for (unsigned j = 0; j < _n; ++j)

    if (!foundMatch) {
      _subsumptionImpossible = true;
      return false;
    } // if (!foundPositiveMatch)
  }   // for (unsigned i = 0; i < _nBaseLits; ++i)

  return true;
} // SATSubsumptionAndResolution::fillMatchesS()

void SATSubsumptionAndResolution::fillMatchesSR()
{
  CALL("SATSubsumptionAndResolution::fillMatchesSR");
  ASS(_L);
  ASS(_M);
  ASS(_m > 0);
  ASS(_n > 0);
  ASS(_matchSet._m == _m);
  ASS(_matchSet._n == _n);
  ASS(_bindingsManager);

  Literal *l_i, *m_j;
  // for one literal in L, store whether it has a positive match in M
  bool foundPositiveMatch = false;
  // for one literal in L, store whether it has a negative match in M
  bool foundNegativeMatch = false;

  // stores whether on all the literals in L there is a negative match in M
  bool hasNegativeMatch = false;

  unsigned lastHeader = numeric_limits<unsigned>::max();
  for (unsigned i = 0; i < _m; ++i) {
    l_i = _L->literals()[i];
    foundPositiveMatch = false;
    foundNegativeMatch = false;
    for (unsigned j = 0; j < _n; ++j) {
      m_j = _M->literals()[j];
      if (l_i->functor() != m_j->functor()) {
        continue;
      }

      if (l_i->polarity() == m_j->polarity()) {
        foundPositiveMatch = checkAndAddMatch(l_i, m_j, i, j, true) || foundPositiveMatch;
      } // end of positive literal match
      // dont check for negative literals if it was established that _sr_impossible
      else if (checkAndAddMatch(l_i, m_j, i, j, false)) {
        hasNegativeMatch = true;
        foundNegativeMatch = true;
      } // end of negative literal matches
    }   // for (unsigned j = 0; j < _nInstanceLits; ++j)

    // Check whether subsumption and subsumption resolution are possible
    if (!foundPositiveMatch) {
      _subsumptionImpossible = true;
      if (!foundNegativeMatch) {
        // no positive or negative matches found
        _srImpossible = true;
        return;
      }
      if (lastHeader == numeric_limits<unsigned>::max()) {
        lastHeader = l_i->header();
        continue;
      }
      else if (lastHeader != l_i->header()) {
        _srImpossible = true;
        return;
      }
    } // if (!foundPositiveMatch)
  }   // for (unsigned i = 0; i < _nBaseLits; ++i)

  if (!hasNegativeMatch) {
    // If there are no negative matches, then the SR is not possible
    _srImpossible = true;
    return;
  }
} // SATSubsumptionAndResolution::fillMatchesSR()

bool SATSubsumptionAndResolution::cnfForSubsumption()
{
  CALL("SATSubsumptionAndResolution::cnfForSubsumption");
  ASS(_L);
  ASS(_M);
  ASS_GE(_matchSet.getMatchCount(), _L->length())
  ASS(!_subsumptionImpossible);

  Solver &solver = _solver->s;

  /**** Completeness ****/
  // Build clauses stating that l_i must be matched to at least one corresponding m_j.
  for (unsigned i = 0; i < _m; ++i) {
    solver.constraint_start();
    for (Match match : _matchSet.getIMatches(i)) {
      if (match._polarity) {
        solver.constraint_push_literal(match._var);
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
      if (match._polarity) {
        solver.constraint_push_literal(match._var);
      }
    }
    auto handle = solver.constraint_end();
    solver.add_atmostone_constraint_unsafe(handle);
  }

  return !solver.inconsistent();
} // SATSubsumptionAndResolution::cnfForSubsumption()

#if SAT_SR_IMPL == 1
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
bool SATSubsumptionAndResolution::cnfForSubsumptionResolution()
{
  CALL("SATSubsumptionResolution::cnfForSubsumptionResolution");
  ASS(_L)
  ASS(_M)
  ASS_GE(_matchSet.getMatchCount(), _L->length())

  Solver &solver = _solver->s;

/**** Existence ****/
#if PRINT_CLAUSE_COMMENTS_SUBS
  cout << "Existence" << endl;
#endif
#if PRINT_CLAUSES_SUBS
  string s = "";
#endif
  vvector<Match> allMatches = _matchSet.getAllMatches();
  solver.constraint_start();
  for (Match match : allMatches) {
    if (!match._polarity) {
      solver.constraint_push_literal(match._var);
#if PRINT_CLAUSES_SUBS
      s += to_string(match._var.index()) + " V ";
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
    if (match1._polarity) {
      continue;
    }
    for (unsigned it2 = it1 + 1; it2 < allMatches.size(); it2++) {
      Match match2 = allMatches[it2];
      if (match2._polarity || match1._j == match2._j) {
        continue;
      }
      solver.constraint_start();
      solver.constraint_push_literal(~match1._var);
      solver.constraint_push_literal(~match2._var);
      auto build = solver.constraint_end();
      solver.add_clause_unsafe(build);
#if PRINT_CLAUSES_SUBS
      cout << ~match1._var << " V " << ~match2._var << endl;
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
      solver.constraint_push_literal(match._var);
#if PRINT_CLAUSES_SUBS
      s += to_string(match._var.index()) + " V ";
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
    vvector<Match> &matches = _matchSet.getJMatches(j);
    for (unsigned i1 = 0; i1 < matches.size(); i1++) {
      Match match1 = matches[i1];
      for (unsigned i2 = i1 + 1; i2 < matches.size(); i2++) {
        Match match2 = matches[i2];
        if (match2._polarity == match1._polarity) {
          continue;
        }
        solver.constraint_start();
        solver.constraint_push_literal(~match1._var);
        solver.constraint_push_literal(~match2._var);
        auto build = solver.constraint_end();
        solver.add_clause_unsafe(build);
#if PRINT_CLAUSES_SUBS
        cout << ~match1._var << " V " << ~match2._var << endl;
#endif
      }
    }
  }
  return !solver.inconsistent();
} // cnfForSubsumptionResolution

#endif
#if SAT_SR_IMPL == 2
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
bool SATSubsumptionAndResolution::cnfForSubsumptionResolution()
{
  CALL("SATSubsumptionResolution::cnfForSubsumptionResolution");
  ASS(_L);
  ASS(_M);
  ASS_GE(_matchSet.getMatchCount(), _L->length())

  Solver &solver = _solver->s;

  /// @brief a vector used to store the sat variables that are subjected to the at most one constraint (will hold the c_j)
  /// The unsigned value is the index of the literal in the instance clause
  static vvector<pair<unsigned, subsat::Var>> atMostOneVars;
  atMostOneVars.clear();

  /**** Existence ****/
#if PRINT_CLAUSES_SUBS
  string s = "";
#endif
  solver.constraint_start();
  for (unsigned j = 0; j < _n; ++j) {
    // Do not add useless variables in the solver
    // It would compromise correctness since a c_j without binding could be true and satisfy c_1 V ... V c_n without making any other clause false.
    if (_matchSet.hasNegativeMatchJ(j)) {
      subsat::Var c_j = solver.new_variable();
      atMostOneVars.push_back(pair<unsigned, subsat::Var>(j, c_j));
      solver.constraint_push_literal(c_j);
#if PRINT_CLAUSES_SUBS
      s += to_string(c_j.index()) + " V ";
#endif
    }
  }
  ASS(!atMostOneVars.empty());
  auto build = solver.constraint_end();
  solver.add_clause_unsafe(build);
#if PRINT_CLAUSES_SUBS
  cout << s.substr(0, s.size() - 3) << endl << endl;
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
    vvector<Match> &matches = _matchSet.getIMatches(i);
    for (Match match : matches) {
#if PRINT_CLAUSES_SUBS
      cout << match._var;
      if (match != matches.back()) {
        cout << " V ";
      }
#endif
      solver.constraint_push_literal(match._var);
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
        if (match._polarity) {
          subsat::Var b_ij = match._var;
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
    vvector<Match> &matches = _matchSet.getJMatches(j);
    subsat::Var c_j = pair.second;
    solver.constraint_start();
    //   (~c_j V b_1j- V ... V b_nj-)
    solver.constraint_push_literal(~c_j);
#if PRINT_CLAUSES_SUBS
    cout << c_j;
#endif
    for (Match match : matches) {
      if (!match._polarity) {
        solver.constraint_push_literal(match._var);
#if PRINT_CLAUSES_SUBS
        cout << " V " << match._var;
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
      if (!match._polarity) {
        solver.constraint_start();
        solver.constraint_push_literal(c_j);
        solver.constraint_push_literal(~match._var);
        auto build = solver.constraint_end();
        solver.add_clause_unsafe(build);
#if PRINT_CLAUSES_SUBS
        cout << c_j << " V " << ~match._var << endl;
#endif
      }
    } // for (Match match : matches)
  } // for (auto &pair : atMostOneVars)
  return !solver.inconsistent();
} // cnfForSubsumptionResolution
#endif

Clause *SATSubsumptionAndResolution::getSubsumptionResolutionConclusion(Clause *M,
                                                                        Literal *m_j,
                                                                        Clause *L)
{
  CALL("SATSubsumptionAndResolution::getSubsumptionResolutionConclusion");
  int mlen = M->length();
  int nlen = mlen - 1;

  Clause *res = new (nlen) Clause(nlen,
                                  SimplifyingInference2(InferenceRule::SUBSUMPTION_RESOLUTION, M, L));

  int next = 0;
  bool found = false;
  for (int i = 0; i < mlen; i++) {
    Literal *curr = (*M)[i];
    // As we will apply subsumption resolution after duplicate literal
    // deletion, the same literal should never occur twice.
    ASS(curr != m_j || !found);
    if (curr != m_j || found) {
      (*res)[next++] = curr;
    }
    else {
      found = true;
    }
  }
  ASS_EQ(next, nlen)

  return res;
}

Clause *SATSubsumptionAndResolution::generateConclusion()
{
  CALL("SATSubsumptionResolution::generateConclusion")
  ASS(_L)
  ASS(_M)
  ASS(_m > 0)
  ASS(_n > 0)
  ASS_EQ(_matchSet._m, _m)
  ASS_EQ(_matchSet._n, _n)
  ASS(_bindingsManager)
  ASS(_model.size() > 0)
  ASS_GE(_matchSet.getMatchCount(), _L->length())

// Provided the solution of the sat solver, we can create the conclusion clause
#if VDEBUG
  unsigned j = numeric_limits<unsigned>::max();
  ;
  // Check that there is only one negative polarity match to j inside the model
  for (subsat::Lit lit : _model) {
    if (lit.is_positive()) {
      // matches can be null if the variable is a c_j
      if (_matchSet.isMatchVar(lit.var())) {
        Match match = _matchSet.getMatchForVar(lit.var());
        if (!match._polarity) {
          if (j == numeric_limits<unsigned>::max()) {
            j = match._j;
          }
          else {
            ASS(j == match._j);
          }
        }
      }
    }
  }
#endif
  unsigned toRemove = numeric_limits<unsigned>::max();
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
        if (!match._polarity) {
          toRemove = match._j;
          break;
        }
      }
    }
  }
  ASS_EQ(_n, _M->size())
  ASS(toRemove != numeric_limits<unsigned>::max());
  return SATSubsumptionAndResolution::getSubsumptionResolutionConclusion(_M, (*_M)[toRemove], _L);
} // SATSubsumptionResolution::generateConclusion

bool SATSubsumptionAndResolution::checkSubsumption(Clause *L,
                                                   Clause *M,
                                                   bool setSR)
{
  CALL("SATSubsumptionAndResolution::checkSubsumption")
  ASS(L)
  ASS(M)

  setupProblem(L, M);

  // Fill the matches
  if (setSR) {
    _srImpossible = pruneSubsumptionResolution();
    _subsumptionImpossible = _srImpossible || pruneSubsumption();

    if (_srImpossible && _subsumptionImpossible) {
      return false;
    }
    else if (_subsumptionImpossible) {
      // subsumption resolution is possible but subsumption is not
      fillMatchesSR();
      return false;
    }
    else {
      ASS(!_srImpossible)
      ASS(!_subsumptionImpossible)
      // both are possible
      fillMatchesSR();
    }
    if (_subsumptionImpossible) {
      return false;
    }
  } // if (setSR)
  else if (pruneSubsumption() || !fillMatchesS()) {
    return false;
  }

  ASS_GE(_matchSet.getMatchCount(), _L->length())

  // Create the constraints for the sat solver
  if (!cnfForSubsumption()) {
    return false;
  }

  // Solve the SAT problem
  Solver &solver = _solver->s;
  solver.theory().setBindings(_bindingsManager);
  return solver.solve() == subsat::Result::Sat;
} // SATSubsumptionAndResolution::checkSubsumption

Clause *SATSubsumptionAndResolution::checkSubsumptionResolution(Clause *L,
                                                                Clause *M,
                                                                bool usePreviousSetUp)
{
  CALL("SATSubsumptionAndResolution::checkSubsumptionResolution");
  ASS(L)
  ASS(M)

  if (usePreviousSetUp) {
    ASS(_L == L);
    ASS(_M == M);
    if (_srImpossible) {
#if PRINT_CLAUSES_SUBS
      cout << "SR impossible" << endl;
#endif
      return nullptr;
    }
    ASS_GE(_matchSet.getMatchCount(), _L->length())
    // do not clear the variables and bindings
    _solver->s.clear_constraints();
  }
  else {
    setupProblem(L, M);
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

  // First set up the clauses
  if (!cnfForSubsumptionResolution()) {
#if PRINT_CLAUSES_SUBS
    cout << "CNF building failed" << endl;
#endif
    return nullptr;
  }

  // Solve the SAT problem
  Solver &solver = _solver->s;
  if (solver.theory().empty()) {
    // -> b_ij implies a certain substitution is valid
    //    for each i, j : b_ij => (S(l_i) = m_j V S(l_i) = ~m_j)
    // These constraints are created in the fillMatches() function by filling the _bindingsManager
    solver.theory().setBindings(_bindingsManager);
  }
  if (solver.solve() != subsat::Result::Sat) {
#if PRINT_CLAUSES_SUBS
    cout << "SAT solver failed" << endl;
#endif
    return nullptr;
  }
  _model.clear();
  solver.get_model(_model);

#if PRINT_CLAUSES_SUBS
  cout << "SAT solver succeeded" << endl;
#endif
  // If the problem is SAT, then generate the conclusion clause
  return generateConclusion();
} // SATSubsumptionAndResolution::checkSubsumptionResolution
