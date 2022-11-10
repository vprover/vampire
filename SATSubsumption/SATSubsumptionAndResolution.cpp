#include "SATSubsumption/SATSubsumptionAndResolution.hpp"
#include "Kernel/Matcher.hpp"
#include "Debug/RuntimeStatistics.hpp"
#include "Util.hpp"
#include <iostream>

using namespace Indexing;
using namespace Kernel;
using namespace SATSubsumption;

/**
 * Updates the first set to hold only the matches that are also in the second set.
 * Assumes that the sets are sorted.
 */
static void intersect(vvector<unsigned> &first, vvector<unsigned> &second)
{
  CALL("SATSubsumptionResolution::intersect")
#ifndef NDEBUG
  for (unsigned i = 1; i < first.size(); i++) {
    ASS(first[i - 1] <= first[i]);
  }
  for (unsigned i = 1; i < second.size(); i++) {
    ASS(second[i - 1] <= second[i]);
  }
#endif
  static vvector<unsigned> result;
  result.clear();
  unsigned i = 0;
  unsigned j = 0;
  while (i < first.size() && j < second.size()) {
    if (first[i] == second[j]) {
      result.push_back(first[i]);
      i++;
      j++;
    }
    else if (first[i] < second[j]) {
      i++;
    }
    else {
      j++;
    }
  }
  first.swap(result);
}

/****************************************************************************/
/*                       SATSubsumptionAndResolution::MatchSet                           */
/****************************************************************************/
SATSubsumptionAndResolution::MatchSet::MatchSet(unsigned m, unsigned n)
    : _iMatches(m),
      _jMatches(n),
#if SAT_SR_IMPL == 1
      _jStates(n / 4 + 1, 0),
#endif
      _m(m),
      _n(n),
      _varToMatch(),
      _referencedMatches(0)
{
  ASS(m > 0);
  ASS(n > 0);
}

SATSubsumptionAndResolution::MatchSet::~MatchSet()
{
  CALL("SATSubsumptionAndResolution::MatchSet::~MatchSet");
}

SATSubsumptionAndResolution::Match SATSubsumptionAndResolution::MatchSet::addMatch(unsigned i, unsigned j, bool polarity, subsat::Var var)
{
  CALL("SATSubsumptionAndResolution::MatchSet::addMatch");
  ASS(i < _m)
  ASS(j < _n)

  Match match(i, j, polarity, var);
  _iMatches[i].push_back(match);
  _jMatches[j].push_back(match);
  unsigned index = match._var.index();
  if (_varToMatch.size() <= index) {
    _varToMatch.resize(index * 2 + 1);
  }
  _varToMatch[index] = match;
  _referencedMatches.push_back(match);
// update the match state
// the wizardry is explained in the header file
#if SAT_SR_IMPL == 1
  if (match._polarity) {
    _jStates[j / 4] |= 1 << (2 * (j % 4));
  }
  else {
    _jStates[j / 4] |= 1 << (2 * (j % 4) + 1);
  }
#endif
  return match;
}

vvector<SATSubsumptionAndResolution::Match> &SATSubsumptionAndResolution::MatchSet::getIMatches(unsigned baseLitIndex)
{
  ASS(baseLitIndex < _m);
  return _iMatches[baseLitIndex];
}

vvector<SATSubsumptionAndResolution::Match> &SATSubsumptionAndResolution::MatchSet::getJMatches(unsigned instanceLitIndex)
{
  ASS(instanceLitIndex < _n);
  return _jMatches[instanceLitIndex];
}

vvector<SATSubsumptionAndResolution::Match> SATSubsumptionAndResolution::MatchSet::getAllMatches()
{
  return _referencedMatches;
}

SATSubsumptionAndResolution::Match SATSubsumptionAndResolution::MatchSet::getMatchForVar(subsat::Var satVar)
{
  CALL("SATSubsumptionAndResolution::MatchSet::getMatchForVar");
  if (satVar.index() >= _referencedMatches.size()) {
    ASS(false);
  }
  return _varToMatch[satVar.index()];
}

bool SATSubsumptionAndResolution::MatchSet::isMatchVar(subsat::Var satVar)
{
  CALL("SATSubsumptionAndResolution::MatchSet::isMatchVar");
  return satVar.index() < _referencedMatches.size();
}

#if SAT_SR_IMPL == 1
bool SATSubsumptionAndResolution::MatchSet::hasPositiveMatchJ(unsigned j)
{
  // the wizardry is explained in the header file
  return (_jStates[j / 4] & (1 << (2 * (j % 4)))) != 0;
}

bool SATSubsumptionAndResolution::MatchSet::hasNegativeMatchJ(unsigned j)
{
  // the wizardry is explained in the header file
  return (_jStates[j / 4] & (2 << (2 * (j % 4)))) != 0;
}
#endif

void SATSubsumptionAndResolution::MatchSet::resize(unsigned newM, unsigned newN)
{
  CALL("SATSubsumptionAndResolution::MatchSet::resize");
  ASS(newM > 0);
  ASS(newN > 0);
  if (newM > _iMatches.size()) {
    _iMatches.resize(newM);
  }
  if (newN > _jMatches.size()) {
    _jMatches.resize(newN);
  }
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
  _varToMatch.clear();
  _referencedMatches.clear();
}

/****************************************************************************/
/*                                 Stats                                    */
/****************************************************************************/
void SATSubsumptionAndResolution::printStats(std::ostream &out)
{
  out << "**** SAT subsumption stats ****" << endl;
}

/****************************************************************************/
/*                    SATSubsumptionAndResolution::SATSubsumptionAndResolution                        */
/****************************************************************************/

SATSubsumptionAndResolution::SATSubsumptionAndResolution() : _L(nullptr),
                                                             _M(nullptr),
                                                             _m(0),
                                                             _n(0),
                                                             _solver(new SolverWrapper()),
                                                             _bindingsManager(new BindingsManager()),
                                                             _atMostOneVars(),
                                                             _matchSet(1, 1),
                                                             _model()
{
// nothing to do
#if WRITE_LITERAL_MATCHES_FILE
  _fileOut.open("subsumptionLiteralLog.txt");
#endif
  // cout << "***SAT subsumption resolution is enabled -- Encoding " << SAT_SR_IMPL << "***" << endl;
}

SATSubsumptionAndResolution::~SATSubsumptionAndResolution()
{
  CALL("SATSubsumptionAndResolution::~SATSubsumptionAndResolution");
  delete _bindingsManager;
#if WRITE_LITERAL_MATCHES_FILE
  _fileOut.close();
#endif
}

void SATSubsumptionAndResolution::setupProblem(Kernel::Clause *L, Kernel::Clause *M)
{
  CALL("SATSubsumptionAndResolution::setupProblem");
  ASS(L);
  ASS(M);
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

  // There cannot be any subsumption resolution, if there isn't at least 2 literals.
  _subsumptionImpossible = L->length() > M->length();
  _srImpossible = false;

  _solver->s.clear();
  _bindingsManager->clear();
}

void SATSubsumptionAndResolution::addBinding(BindingsManager::Binder *binder, unsigned i, unsigned j, bool polarity)
{
  CALL("SATSubsumptionAndResolution::addBinding");
  ASS(i < _m);
  ASS(j < _n);
  subsat::Var satVar = _solver->s.new_variable();
#if PRINT_CLAUSES_SUBS
  cout << satVar << " -> (" << i << " " << j << " " << (polarity ? "+" : "-") << ")" << endl;
#endif
  _matchSet.addMatch(i, j, polarity, satVar);
  _bindingsManager->commit_bindings(*binder, satVar, i, j);
}

bool SATSubsumptionAndResolution::checkAndAddMatch(Literal *L_i, Literal *M_j, unsigned i, unsigned j, bool polarity)
{
  CALL("SATSubsumptionAndResolution::checkAndAddMatch");
#if WRITE_LITERAL_MATCHES_FILE
  _fileOut << L_i->getId() << " " << M_j->getId();
#endif
  if (L_i->arity() == 0) {
#if WRITE_LITERAL_MATCHES_FILE
    _fileOut << " 1" << endl;
#endif
    return true;
  }

  bool match = false;
  {
    auto binder = _bindingsManager->start_binder();
    if (MatchingUtils::matchArgs(L_i, M_j, binder)) {
      addBinding(&binder, i, j, polarity);
      match = true;
    }
  }
  if (L_i->commutative()) {
    auto binder = _bindingsManager->start_binder();
    if (MatchingUtils::matchReversedArgs(L_i, M_j, binder)) {
      addBinding(&binder, i, j, polarity);
      match = true;
    }
  }
#if WRITE_LITERAL_MATCHES_FILE
  if (match) {
    _fileOut << " 1" << endl;
  }
  else {
    _fileOut << " 0" << endl;
  }
#endif
  return match;
}

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

  Literal *L_i, *M_j;

  // number of matches found - is equal to the number of variables in the SAT solver
  for (unsigned i = 0; i < _m; ++i) {
    L_i = _L->literals()[i];
    bool foundPositiveMatch = false;

    for (unsigned j = 0; j < _n; ++j) {
      M_j = _M->literals()[j];
      if (L_i->functor() != M_j->functor() || L_i->polarity() != M_j->polarity()) {
        continue;
      }
      if (checkAndAddMatch(L_i, M_j, i, j, true)) {
        foundPositiveMatch = true;
      }
    } // for (unsigned j = 0; j < _n; ++j)

    if (!foundPositiveMatch) {
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

  Literal *L_i, *M_j;
  bool foundPositiveMatch = false;

  // used ot check that the SR is even possible
  // the intersection represents the set of M_j that have been matched only negatively by some L_i
  bool hasNegativeMatch = false;

  unsigned lastHeader = numeric_limits<unsigned>::max();
  for (unsigned i = 0; i < _m; ++i) {
    L_i = _L->literals()[i];
    foundPositiveMatch = false;
    _negativeMatches.clear();

    for (unsigned j = 0; j < _n; ++j) {
      M_j = _M->literals()[j];
      if (L_i->functor() != M_j->functor()) {
        continue;
      }

      if (L_i->polarity() == M_j->polarity()) {
        if (checkAndAddMatch(L_i, M_j, i, j, true)) {
          foundPositiveMatch = true;
        }
      } // end of positive literal match
      // dont check for negative literals if it was established that _sr_impossible
      else if (!_srImpossible && checkAndAddMatch(L_i, M_j, i, j, false)) {
        hasNegativeMatch = true;
        if (!foundPositiveMatch) {
          // no need to push back if we already found a positive match
          _negativeMatches.push_back(j);
        }
      } // end of negative literal matches
    }   // for (unsigned j = 0; j < _nInstanceLits; ++j)

    if (!foundPositiveMatch) {
      _subsumptionImpossible = true;
      if (!hasNegativeMatch) {
        // no positive or negative matches found
        _srImpossible = true;
        return;
      }
      if (lastHeader == numeric_limits<unsigned>::max()) {
        lastHeader = L_i->header();
        // set up the first intersection
        _intersection.clear();
        _intersection.insert(_intersection.end(), _negativeMatches.begin(), _negativeMatches.end());
        continue;
      }
      else if (lastHeader != L_i->header()) {
        _srImpossible = true;
        return;
      }

      intersect(_intersection, _negativeMatches);
      if (_intersection.empty()) {
        // It is impossible to find a SR because some L_i have no possible match
        _srImpossible = true;
        return;
      }
      if (_subsumptionImpossible && _srImpossible) {
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

  Solver &solver = _solver->s;
  solver.theory().setBindings(_bindingsManager);

  // Build clauses stating that L_i must be matched to at least one corresponding M_j.
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
}

#if SAT_SR_IMPL == 1
/**
 * First encoding of the sat subsumption resolution
 *
 * @pre assumes that base and instance literals are set
 *
 * Let the base clause be L and the instance clause be M.
 *  - We name the literals in L as L1, L2, ..., Ln
 *  - We name the literals in M as M1, M2, ..., Mk
 *
 * We introduce the variables
 *  - b_ij+ if L_i has a substitution S such that S(L_i) = M_j
 *    we will say that b_ij+ as a positive polarity
 *  - b_ij- if L_i has a substitution S such that S(L_i) = ~M_j
 *    we will say that b_ij- as a negative polarity
 *  - c_j if M_j is matched by at least one negative polarity variable b_ij-
 * b_ij+ and b_ij- are mutually existentially exclusive, therefore, we only introduce one variable b_ij for the sat solver, and remember its polarity.
 * It may be that both b_ij+ and b_ij- do not exist.
 *
 *
 * We introduce the following subsumption resolution clauses clauses:
 *  - At least one negative polarity match exists
 *    c_1 V c_2 V ... V c_n
 *  - At most one M_j is matched by a negative polarity variable
 *    At most one c_j is true (embedded in the sat solver)
 *    (~c_1 V ~c_2) /\ (~c_1 V ~c_3) /\ ... /\ (~c_2 V ~c_3) /\ ...
 *  - Each L_i is matched by at least one M_j
 *    b_11 V ... V b_1k /\ b_21 V ... V b_2k /\ ... /\ b_n1 V ... V b_nk
 *  - c_j is true if and only if there is a negative polarity match b_ij-
 *    for each j : c_j <=> b_ij- for some i
 *    for each j :(~c_j V b_1j V ... V b_nj)
 *             /\ (c_j V ~b_1j) /\ ... /\ (c_j V ~bnj)
 *  - if c_j is true, then there is no positive polarity match b_ij+
 *    for each i,j : (~c_j V ~b_ij+)
 *  - b_ij implies a certain substitution is valid
 *    for each i, j : b_ij => (S(L_i) = M_j V S(L_i) = ~M_j)
 *
 */
bool SATSubsumptionAndResolution::cnfForSubsumptionResolution()
{
  CALL("SATSubsumptionResolution::cnfForSubsumptionResolution");
  ASS(_L);
  ASS(_M);
  ASS(_solver->s.theory().empty());
  // Checks for all the literal mappings and store them in a cache
  // nVar is the number of variables that are of the form b_ij

  // -> b_ij implies a certain substitution is valid
  //    for each i, j : b_ij => (S(L_i) = M_j V S(L_i) = ~M_j)
  // These constraints are created in the fillMatches() function by filling the _bindingsManager
  Solver &solver = _solver->s;
  solver.theory().setBindings(_bindingsManager);

  // Set up the _atMostOneVars vectors to store the c_j
  if (_atMostOneVars.capacity() < _n) {
    _atMostOneVars.reserve(_n);
  }
  _atMostOneVars.clear();
  // Create the set of clauses

  // -> At least one negative polarity match exists
  //    c_1 V ... V c_n
#if PRINT_CLAUSES_SUBS
  string s = "";
#endif
  solver.constraint_start();
  for (unsigned j = 0; j < _n; ++j) {
    // Do not add useless variables in the solver
    // It would compromise correctness since a c_j without binding could be true and satisfy c_1 V ... V c_n without making any other clause false.
    if (_matchSet.hasNegativeMatchJ(j)) {
      subsat::Var c_j = solver.new_variable();
      _atMostOneVars.push_back(pair<unsigned, subsat::Var>(j, c_j));
      solver.constraint_push_literal(c_j);
#if PRINT_CLAUSES_SUBS
      s += to_string(c_j.index()) + " V ";
#endif
    }
  }
  auto build = solver.constraint_end();
  solver.add_clause_unsafe(build);
#if PRINT_CLAUSES_SUBS
  cout << s.substr(0, s.size() - 3) << endl;
#endif
#if PRINT_CLAUSES_SUBS
  cout << endl;
#endif
  // add the c_1 V ... V c_n clause
  // -> At most one M_j is matched by a negative polarity variable
  //    At most one c_j is true (embedded in the sat solver)
  solver.constraint_start();
  for (auto var : _atMostOneVars) {
    solver.constraint_push_literal(var.second);
  }
  build = solver.constraint_end();
  solver.add_atmostone_constraint(build);
  // -> Each L_i is matched by at least one M_j
  //    b_11 V ... V b_1k
  // /\ b_21 V ... V b_2k
  // /\ ...
  // /\ b_n1 V ... V b_nk
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

  //  -> if c_j is true, then there is no positive polarity match b_ij+
  //     for each i,j : (~c_j V ~b_ij+)
  for (auto var : _atMostOneVars) {
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

  // -> c_j is true if and only if there is a negative polarity match b_ij-
  //    for each j : c_j <=> b_ij- for some i
  //    for each j :(~c_j V b_1j- V ... V b_nj-)
  //            /\ (c_j V ~b_1j-) /\ ... /\ (c_j V ~b_nj-)
  for (auto &pair : _atMostOneVars) {
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
    }
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
    }
  }
  return !solver.inconsistent();
} // cnfForSubsumptionResolution

#else // SAT_SR_IMPL == 2
/**
 * Second encoding of the sat subsumption resolution
 *
 * @pre assumes that base and instance literals are set, the match set is empty and the solver is empty
 *
 * Let the base clause be L and the instance clause be M.
 *  - We name the literals in L as L1, L2, ..., Ln
 *  - We name the literals in M as M1, M2, ..., Mk
 *
 * We introduce the variables
 *  - b_ij+ if L_i has a substitution S such that S(L_i) = M_j
 *    we will say that b_ij+ as a positive polarity
 *  - b_ij- if L_i has a substitution S such that S(L_i) = ~M_j
 *    we will say that b_ij- as a negative polarity
 * b_ij+ and b_ij- are mutually existentially exclusive, therefore, we only introduce one variable b_ij for the sat solver, and remember its polarity.
 * It may be that both b_ij+ and b_ij- do not exist.
 *
 *
 * We introduce the following subsumption resolution clauses clauses:
 *  - At least one negative polarity match exists
 *    b_11- V ... V b_1m- V ... V b_n1 V ... V b_nm-
 *  - Each L_i is matched by at least one M_j
 *    b_11 V ... V b_1k /\ b_21 V ... V b_2k /\ ... /\ b_n1 V ... V b_nk
 *  - At most one M_j is matched by a negative polarity variable
 *    for each j : b_1j- V ... V b_nj- => ~b_ij', j' != j
 *  - b_ij implies a certain substitution is valid
 *    for each i, j : b_ij => (S(L_i) = M_j V S(L_i) = ~M_j)
 *
 */
bool SATSubsumptionAndResolution::cnfForSubsumptionResolution()
{
  CALL("SATSubsumptionResolution::cnfForSubsumptionResolution");
  ASS(_L);
  ASS(_M);

  // -> b_ij implies a certain substitution is valid
  //    for each i, j : b_ij => (S(L_i) = M_j V S(L_i) = ~M_j)
  // These constraints are created in the fillMatches() function by filling the _bindingsManager
  Solver &solver = _solver->s;
  solver.theory().setBindings(_bindingsManager);

// -> At least one negative polarity match exists
//    b_11- V ... V b_1m- V ... V b_n1 V ... V b_nm-
#if PRINT_CLAUSE_COMMENTS_SUBS
  cout << "At least one negative polarity match exists" << endl;
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

// -> Each L_i is matched by at least one M_j
//    b_11 V ... V b_1k
// /\ b_21 V ... V b_2k
// /\ ...
// /\ b_n1 V ... V b_nk
#if PRINT_CLAUSE_COMMENTS_SUBS
  cout << "Each L_i is matched by at least one M_j" << endl;
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

// -> If M_j is matched negatively, then all the other matches to M_j are also negative
//    for each j, forall i, forall i', ~b_ij V ~b_ij'
#if PRINT_CLAUSE_COMMENTS_SUBS
  cout << "If M_j is matched negatively, then all the other matches to M_j are also negative" << endl;
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

// -> At most one M_j is matched by a negative polarity variable
//    for each j : b_1j- V ... V b_nj- => ~b_ij', j' != j
#if PRINT_CLAUSE_COMMENTS_SUBS
  cout << "At most one M_j is matched by a negative polarity variable" << endl;
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
  return !solver.inconsistent();
} // cnfForSubsumptionResolution

#endif

/**
 * Creates a new clause that is the result of the subsumption resolution
 * of the base and instance clauses.
 *
 * This process is achieved using the output of the sat solver. Search for the negative polarity match and remove the M_j from the clause.
 *
 * Assumes that the solver has already been called and that the model is already stored in _model.
 */
Kernel::Clause *SATSubsumptionAndResolution::generateConclusion()
{
  CALL("SATSubsumptionResolution::generateConclusion");
  ASS(_L);
  ASS(_M);
  ASS(_m > 0);
  ASS(_n > 0);
  ASS(_matchSet._m == _m);
  ASS(_matchSet._n == _n);
  ASS(_bindingsManager);
  ASS(_model.size() > 0);

// Provided the solution of the sat solver, we can create the conclusion clause
#if VDEBUG
  unsigned j = 0;
  // Check that there is only one negative polarity match to j inside the model
  for (subsat::Lit lit : _model) {
    if (lit.is_positive()) {
      // matches can be null if the variable is a c_j
      if (_matchSet.isMatchVar(lit.var())) {
        Match match = _matchSet.getMatchForVar(lit.var());
        if (!match._polarity) {
          if (j == 0) {
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
  // Create the conclusion clause
  Kernel::Clause *conclusion = new (_n - 1) Kernel::Clause(_n - 1,
                                                           SimplifyingInference2(InferenceRule::SUBSUMPTION_RESOLUTION, _M, _L));
  unsigned k = 0;
  for (unsigned j = 0; j < _n; ++j) {
    if (j != toRemove) {
      conclusion->literals()[k++] = _M->literals()[j];
    }
  }
  ASS(k == _n - 1);
  return conclusion;
}

bool SATSubsumptionAndResolution::checkSubsumption(Kernel::Clause *L, Kernel::Clause *M, bool setSR)
{
  CALL("SATSubsumptionAndResolution::checkSubsumption");
  if (L->length() > M->length()) {
    return false;
  }

  setupProblem(L, M);

  // Fill the matches
  if (setSR && !_srImpossible) {
    fillMatchesSR();
    if (_subsumptionImpossible) {
      return false;
    }
  }
  else if (_subsumptionImpossible || !fillMatchesS()) {
    return false;
  }

  if (!cnfForSubsumption()) {
    return false;
  }
  // Solve the SAT problem
  if (_solver->s.solve() == subsat::Result::Sat) {
    return true;
  }
  return false;
}

Kernel::Clause *SATSubsumptionAndResolution::checkSubsumptionResolution(Kernel::Clause *L, Kernel::Clause *M, bool usePreviousSetUp)
{
  CALL("SATSubsumptionAndResolution::checkSubsumptionResolution");
  if (M->length() < L->length()) {
    return nullptr;
  }
#if VDEBUG
  if (usePreviousSetUp) {
    ASS(_L == L);
    ASS(_M == M);
  }
#endif

  // Checks for all the literal mappings and store them in a cache
  // nVar is the number of variables that are of the form b_ij
  if (!usePreviousSetUp) {
    setupProblem(L, M);
    if (_srImpossible) {
#if PRINT_CLAUSES_SUBS
      cout << "Setup failed" << endl;
#endif
      return nullptr;
    }
    fillMatchesSR();
  }
  else {
    // Remove the potentially added clauses from the solver.
    // Some clauses could have been added if it uses the previous setup.
    _solver->s.clear();
    // now reallocates the variables
    for (unsigned i = 0; i < _matchSet._referencedMatches.size(); i++) {
      _solver->s.new_variable();
    }
  }

  if (_srImpossible) {
#if PRINT_CLAUSES_SUBS
    cout << "SR impossible" << endl;
#endif
    return nullptr;
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
  if (solver.solve() != subsat::Result::Sat) {
#if PRINT_CLAUSES_SUBS
    cout << "SAT solver failed" << endl;
#endif
    return nullptr;
  }
  _model.clear();
  solver.get_model(_model);

  // If the problem is SAT, then generate the conclusion clause
  return generateConclusion();
}
