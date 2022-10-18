#include "SATSubsumptionResolution.hpp"
#include "Kernel/Matcher.hpp"
#include "Debug/RuntimeStatistics.hpp"
#include "Util.hpp"
#include <iostream>

using namespace Indexing;
using namespace Kernel;
using namespace SMTSubsumption;

#define SAT_SR_IMPL 2

/**
 * Updates the first set to hold only the matches that are also in the second set.
 * Assumes that the sets are sorted.
 */
static void intersect(vvector<unsigned> &first, vvector<unsigned> &second)
{
  #ifndef NDEBUG
  for (unsigned i = 1; i < first.size(); i++) {
    ASS(first[i-1] <= first[i]);
  }
  for (unsigned i = 1; i < second.size(); i++) {
    ASS(second[i-1] <= second[i]);
  }
  #endif
  vvector<unsigned> result;
  result.reserve(first.size());
  unsigned i = 0;
  unsigned j = 0;
  while (i < first.size() && j < second.size()) {
    if (first[i] == second[j]) {
      result.push_back(first[i]);
      i++;
      j++;
    } else if (first[i] < second[j]) {
      i++;
    } else {
      j++;
    }
  }
  first.swap(result);
}

/****************************************************************************/
/*                       SATSubsumption::MatchSet                           */
/****************************************************************************/
SATSubsumption::MatchSet::MatchSet(unsigned m, unsigned n)
    : _iMatches(m),
      _jMatches(n),
      _iStates(m / 4 + 1, 0),
      _jStates(n / 4 + 1, 0),
      _m(m),
      _n(n),
      _varToMatch(),
      _nUsedMatches(0),
      _nAllocatedMatches(1),
      _allocatedMatches(nullptr)
{
  ASS(m > 0);
  _allocatedMatches = (Match**) malloc(_nAllocatedMatches * sizeof(Match*));
  _allocatedMatches[0] = (Match*) malloc(sizeof(Match));
}

SATSubsumption::MatchSet::~MatchSet()
{
  for (unsigned i = 1; i < _nAllocatedMatches; i *= 2) {
    free(_allocatedMatches[i]);
  }
  free(_allocatedMatches);
}

SATSubsumption::Match *SATSubsumption::MatchSet::allocateMatch()
{
  ASS(_nUsedMatches <= _nAllocatedMatches);
  if (_nUsedMatches == _nAllocatedMatches) {
    _nAllocatedMatches *= 2;
    _allocatedMatches = (Match **) realloc(_allocatedMatches, _nAllocatedMatches * sizeof(Match*));

    Match* newMatches = (Match*) malloc((_nAllocatedMatches - _nUsedMatches) * sizeof(Match));
    for (unsigned i = 0; i < _nAllocatedMatches - _nUsedMatches; i++) {
      _allocatedMatches[_nUsedMatches + i] = newMatches + i;
    }
  }
  return _allocatedMatches[_nUsedMatches++];
}

SATSubsumption::Match *SATSubsumption::MatchSet::addMatch(unsigned i, unsigned j, bool polarity, subsat::Var var)
{
  ASS(i < _m);
  ASS(j < _n);

  Match* match = allocateMatch();
  *match = Match(i, j, polarity, var);
  _iMatches[i].push_back(match);
  _jMatches[j].push_back(match);
  unsigned index = match->_var.index();
  if (_varToMatch.size() <= index) {
    _varToMatch.resize(index * 2 + 1);
  }
  _varToMatch[index] = match;
  // update the match state
  // the wizardry is explained in the header file
  if (match->_polarity) {
    _iStates[i / 4] |= 1 << (2 * (i % 4));
    _jStates[j / 4] |= 1 << (2 * (j % 4));
  } else {
    _iStates[i / 4] |= 1 << (2 * (i % 4) + 1);
    _jStates[j / 4] |= 1 << (2 * (j % 4) + 1);
  }
  return match;
}

vvector<SATSubsumption::Match *> &SATSubsumption::MatchSet::getIMatches(unsigned baseLitIndex)
{
  ASS(baseLitIndex < _m);
  return _iMatches[baseLitIndex];
}

vvector<SATSubsumption::Match *> &SATSubsumption::MatchSet::getJMatches(unsigned instanceLitIndex)
{
  ASS(instanceLitIndex < _n);
  return _jMatches[instanceLitIndex];
}

vvector<SATSubsumption::Match *> SATSubsumption::MatchSet::getAllMatches()
{
  vvector<SATSubsumption::Match*> result(_allocatedMatches, _allocatedMatches + _nUsedMatches);
  return result;
}

SATSubsumption::Match *SATSubsumption::MatchSet::getMatchForVar(subsat::Var satVar)
{

  if (satVar.index() >= _nUsedMatches) {
    return nullptr;
  }
  Match* match = _varToMatch[satVar.index()];
  ASS(match != nullptr);
  return match;
}

bool SATSubsumption::MatchSet::hasPositiveMatchI(unsigned i) {
  // the wizardry is explained in the header file
  return (_iStates[i / 4] & (1 << (2 * (i % 4)))) != 0;
}

bool SATSubsumption::MatchSet::hasNegativeMatchI(unsigned i) {
  // the wizardry is explained in the header file
  return (_iStates[i / 4] & (2 << (2 * (i % 4)))) != 0;
}

bool SATSubsumption::MatchSet::hasPositiveMatchJ(unsigned j) {
  // the wizardry is explained in the header file
  return (_jStates[j / 4] & (1 << (2 * (j % 4)))) != 0;
}

bool SATSubsumption::MatchSet::hasNegativeMatchJ(unsigned j) {
  // the wizardry is explained in the header file
  return (_jStates[j / 4] & (2 << (2 * (j % 4)))) != 0;
}

void SATSubsumption::MatchSet::resize(unsigned newM, unsigned newN)
{
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

  if (newM / 4 + 1 > _iStates.size()) {
    _iStates.resize(newM / 4 + 1, 0);
  }
  if (newN / 4 + 1 > _jStates.size()) {
    _jStates.resize(newN / 4 + 1, 0);
  }
}

void SATSubsumption::MatchSet::clear()
{
  for (unsigned i = 0; i < _m; i++) {
    _iMatches[i].clear();
  }
  for (unsigned j = 0; j < _n; j++) {
    _jMatches[j].clear();
  }
  _nUsedMatches = 0;
  _varToMatch.clear();

  fill(_iStates.begin(), _iStates.end(), 0);
  fill(_jStates.begin(), _jStates.end(), 0);
}

/****************************************************************************/
/*                    SATSubsumption::SATSubsumption                        */
/****************************************************************************/

SATSubsumption::SATSubsumption() :
  _L(nullptr),
  _M(nullptr),
  _m(0),
  _n(0),
  _solver(new SolverWrapper()),
  _bindingsManager(new BindingsManager()),
  _atMostOneVars(),
  _matchSet(1, 1),
  _model(),
  _nSubsumptionCalls(0),
  _nSubsumptionResolutionCalls(0),
  _nSubsumptionSolverCalls(0),
  _nSubsumptionResolutionSolverCalls(0)
{
  // nothing to do

}

SATSubsumption::~SATSubsumption()
{
  delete _bindingsManager;
  cerr << "SATSubsumption: " << _nSubsumptionCalls << " subsumption calls, " << _nSubsumptionResolutionCalls << " resolution calls, " << _nSubsumptionSolverCalls << " solver calls, " << _nSubsumptionResolutionSolverCalls << " resolution solver calls" << endl;
}

void SATSubsumption::setupProblem(Kernel::Clause* L, Kernel::Clause* M)
{
  CALL("SATSubsumption::setupProblem");
  //cerr << "Setting up problem " << L->toString() << " & " << M->toString() << endl;
  _L = L;
  _M = M;
  _m = L->length();
  _n = M->length();

  _matchSet.clear();
  _matchSet.resize(_m, _n);

  _solver->s.clear();
  _bindingsManager->clear();
}

void SATSubsumption::addBinding(BindingsManager::Binder *binder, unsigned i, unsigned j, bool polarity)
{
  ASS(i < _m);
  ASS(j < _n);
  subsat::Var satVar = _solver->s.new_variable();
  _matchSet.addMatch(i, j, polarity, satVar);
  _bindingsManager->commit_bindings(*binder, satVar, i, j);
}

bool SATSubsumption::checkAndAddMatch(Literal* L_i, Literal* M_j, unsigned i, unsigned j, bool polarity) {
  CALL("SATSubsumption::checkAndAddMatch");
  if (!Literal::headersMatch(L_i, M_j, !polarity)) {
    return false;
  }

  bool match = false;
    // Need to use the matchNoSwap function to avoid having twice the same binding
    // (e.g L_i : f(x) == g(y)  M_j : g(c) == f(d), if using match, we would have twice the binding {x -> d, y -> c})
  {
    auto binder = _bindingsManager->start_binder();
    if (MatchingUtils::matchNoSwap(L_i, M_j, !polarity, binder)) {
      addBinding(&binder, i, j, polarity);
      match = true;
    }
  }
  if(L_i->commutative()) {
    auto binder = _bindingsManager->start_binder();
    if (MatchingUtils::swapMatch(L_i, M_j, !polarity, binder)) {
      addBinding(&binder, i, j, polarity);
      match = true;
    }
  }
  return match;
}

bool SATSubsumption::fillMatchesS()
{
  CALL("SATSubsumption::fillMatchesS");
  ASS(_L);
  ASS(_M);
  ASS(_m > 0);
  ASS(_n > 0);
  ASS(_matchSet._m == _m);
  ASS(_matchSet._n == _n);
  ASS(_bindingsManager);

  // number of matches found - is equal to the number of variables in the SAT solver
  for (unsigned i = 0; i < _m; ++i)
  {
    Literal* L_i = _L->literals()[i];
    //cerr << "Checking literal " << L_i->toString() << endl;
    bool foundPositiveMatch = false;

    for (unsigned j = 0; j < _n; ++j)
    {
      Literal* M_j = _M->literals()[j];

      if (Literal::headersMatch(L_i, M_j, false)
       && L_i->polarity() == M_j->polarity()
       && checkAndAddMatch(L_i, M_j, i, j, true)) {
        foundPositiveMatch = true;
      }
    } // for (unsigned j = 0; j < _n; ++j)

    if (!foundPositiveMatch) {
      return false;
    } // if (!foundPositiveMatch)
  } // for (unsigned i = 0; i < _nBaseLits; ++i)

  return true;
} // SATSubsumption::fillMatchesS()

bool SATSubsumption::fillMatchesSR()
{
  CALL("SATSubsumption::fillMatchesSR");
  ASS(_L);
  ASS(_M);
  ASS(_m > 0);
  ASS(_n > 0);
  ASS(_matchSet._m == _m);
  ASS(_matchSet._n == _n);
  ASS(_bindingsManager);

  // used ot check that the SR is even possible
  // the intersection represents the set of M_j that have been matched only negatively by some L_i
  vvector<unsigned> intersection;

  // for some L_i, stores the set of M_j that have been negatively matched by L_i
  vvector<unsigned> negativeMatches = vvector<unsigned>(_n);

  bool hasNegativeMatch = false;

  unsigned lastHeader = numeric_limits<unsigned>::max();
  for (unsigned i = 0; i < _m; ++i)
  {
    Literal* L_i = _L->literals()[i];
    bool foundPositiveMatch = false;
    negativeMatches.clear();

    for (unsigned j = 0; j < _n; ++j)
    {
      Literal* M_j = _M->literals()[j];
      if(L_i->polarity() == M_j->polarity())
      {
        if (checkAndAddMatch(L_i, M_j, i, j, true)) {
          foundPositiveMatch = true;
        }
      } // end of positive literal match
      else {
        if (checkAndAddMatch(L_i, M_j, i, j, false)) {
          negativeMatches.push_back(j);
          hasNegativeMatch = true;
        }
      } // end of negative literal matches
    } // for (unsigned j = 0; j < _nInstanceLits; ++j)

    if (!foundPositiveMatch) {
      if (!hasNegativeMatch) {
        // no positive or negative matches found
        return false;
      }
      // If the headers are different, then the SR is impossible
      if (lastHeader == numeric_limits<unsigned>::max()) {
        lastHeader = L_i->header();
        // set up the first intersection
        intersection = vvector<unsigned>(negativeMatches);
        continue;
      } else if (lastHeader != L_i->header()) {
        return false;
      }

      intersect(intersection, negativeMatches);
      if (intersection.empty()) {
        // It is impossible to find a SR because some L_i have no possible match
        return false;
      }
    } // if (!foundPositiveMatch)
  } // for (unsigned i = 0; i < _nBaseLits; ++i)

  if (!hasNegativeMatch) {
    // If there are no negative matches, then the SR is not possible
    return false;
  }
  return true;
} // SATSubsumption::fillMatchesSR()

bool SATSubsumption::cnfForSubsumption()
{
  CALL("SATSubsumption::cnfForSubsumption");
  ASS(_L);
  ASS(_M);
  ASS(_solver->s.theory().empty());

  Solver& solver = _solver->s;
  solver.theory().setBindings(_bindingsManager);

  // Build clauses stating that L_i must be matched to at least one corresponding M_j.
  for (unsigned i = 0; i < _m; ++i) {
    solver.constraint_start();
    for (Match* match : _matchSet.getIMatches(i)) {
      if (match->_polarity) {
        solver.constraint_push_literal(match->_var);
      }
    }
    auto handle = solver.constraint_end();
    solver.add_clause_unsafe(handle);
  }

  // Here we store the AtMostOne constraints saying that each instance literal may be matched at most once.
  // Each instance literal can be matched by at most 2 boolean vars per base literal (two orientations of equalities).
  // NOTE: instance constraints cannot be packed densely because we only know their shape at the end.
  // uint32_t const instance_constraint_maxsize = 2 * base_len;
  for(unsigned j = 0; j < _m; ++j) {
    solver.constraint_start();
    for (Match* match : _matchSet.getJMatches(j)) {
      if (match->_polarity) {
        solver.constraint_push_literal(match->_var);
      }
    }
    auto handle = solver.constraint_end();
    solver.add_atmostone_constraint_unsafe(handle);
  }

  return !solver.inconsistent();
}

bool SATSubsumption::checkSubsumption(Kernel::Clause* L, Kernel::Clause* M)
{
  //cerr << "checkSubsumption(" << L->toString() << ", " << M->toString() << ")" << endl;
  CALL("check Subsumption");
  if(++_nSubsumptionCalls % 100000 == 0) {
    cerr << "check Subsumption : " << _nSubsumptionCalls << " calls" << endl;
  }
  if(L->length() > M->length()) {
    return false;
  }

  setupProblem(L, M);

  // Fill the matches
  if (!fillMatchesS()) {
    return false;
  }

  if(!cnfForSubsumption()) {
    return false;
  }

  if(++_nSubsumptionSolverCalls % 10000 == 0) {
    cerr << "checkSubsumption Solver : " << _nSubsumptionSolverCalls << " calls" << endl;
  }
  // Solve the SAT problem
  if(_solver->s.solve() == subsat::Result::Sat) {
    //cerr << "Subsumes" << endl;
    return true;
  }
  return false;
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
 *    At most one c_j is true (embeded in the sat solver)
 *    (~c_1 V ~c_2) /\ (~c_1 V ~c_3) /\ ... /\ (~c_2 V ~c_3) /\ ...
 *  - Each L_i is matched by at least one M_j
 *    b_11 V ... V b_1k /\ b_21 V ... V b_2k /\ ... /\ b_n1 V ... V b_nk
 *  - c_j is true if and only if there is a negative polarity match b_ij-
 *    for each j : c_j <=> b_ij- for some i
 *    for each j :(~c_j V b_1j V ... V b_nj)
 *             /\ (c_j V ~b_1j) /\ ... /\ (c_j V ~bnj)
 *  - b_ij implies a certain substitution is valid
 *    for each i, j : b_ij => (S(L_i) = M_j V S(L_i) = ~M_j)
 *
 */
bool SATSubsumption::cnfForSubsumptionResolution()
{
  CALL("SATSubsumptionResolution::cnfForSubsumptionResolution");
  ASS(_L);
  ASS(_M);
  ASS(_solver->s.theory().empty());
  // Checks for all the literal mapings and store them in a cache
  // nVar is the number of variables that are of the form b_ij

  // -> b_ij implies a certain substitution is valid
  //    for each i, j : b_ij => (S(L_i) = M_j V S(L_i) = ~M_j)
  // These constraints are created in the fillMatches() function by filling the _bindingsManager
  Solver& solver = _solver->s;
  solver.theory().setBindings(_bindingsManager);

  // Set up the _atMostOneVars vectors to store the c_j
  if(_atMostOneVars.capacity() < _n) {
    _atMostOneVars.reserve(_n);
  }
  _atMostOneVars.clear();
  // Create the set of clauses

  // -> At least one negative polarity match exists
  //    c_1 V c_2 V ... V c_n
  solver.constraint_start();
  for (unsigned j = 0; j < _n; ++j) {
    // Do not add useless variables in the solver
    // It would compromise correctness since a c_j without binding coud be true and satisfy c_1 V ... V c_n without making any other clause false.
    if(_matchSet.hasNegativeMatchJ(j)) {
      subsat::Var c_j = solver.new_variable();
      _atMostOneVars.push_back(pair<unsigned, subsat::Var>(j, c_j));
      solver.constraint_push_literal(c_j);
    }
  }
  auto build = solver.constraint_end();
  solver.add_clause_unsafe(build);
  // add the c_1 V ... V c_n clause
  // -> At most one M_j is matched by a negative polarity variable
  //    At most one c_j is true (embeded in the sat solver)
  solver.constraint_start();
  for (auto var : _atMostOneVars) {
    solver.constraint_push_literal(var.second);
  }
  build = solver.constraint_end();
  solver.add_atmostone_constraint_unsafe(build);

  // -> Each L_i is matched by at least one M_j
  //    b_11 V ... V b_1k
  // /\ b_21 V ... V b_2k
  // /\ ...
  // /\ b_n1 V ... V b_nk
  for (unsigned i = 0; i < _m; ++i) {
    solver.constraint_start();
    vvector<Match*> &matches = _matchSet.getIMatches(i);
    for (Match *match : matches) {
      if (match != matches.back()) {
      }
      solver.constraint_push_literal(match->_var);
    }
    auto build = solver.constraint_end();
    solver.add_clause_unsafe(build);
  }

  // -> c_j is true if and only if there is a negative polarity match b_ij-
  //    for each j : c_j <=> b_ij- for some i
  //    for each j :(~c_j V b_1j- V ... V b_nj-)
  //            /\ (c_j V ~b_1j-) /\ ... /\ (c_j V ~b_nj-)
  for (auto &pair : _atMostOneVars) {
    unsigned j = pair.first;
    vvector<Match*> &matches = _matchSet.getJMatches(j);
    subsat::Var c_j = pair.second;
    solver.constraint_start();
    //   (~c_j V b_1j- V ... V b_nj-)
    solver.constraint_push_literal(~c_j);
    for (Match* match : matches) {
      if (!match->_polarity) {
        solver.constraint_push_literal(match->_var);
      }
    }
    auto build = solver.constraint_end();
    solver.add_clause_unsafe(build);
    //   (c_j V ~b_1j-) /\ ... /\ (c_j V ~b_nj-)
    for (Match* match : matches) {
      if (!match->_polarity) {
        solver.constraint_start();
        solver.constraint_push_literal(c_j);
        solver.constraint_push_literal(~match->_var);
        auto build = solver.constraint_end();
        solver.add_clause_unsafe(build);
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
bool SATSubsumption::cnfForSubsumptionResolution()
{
  CALL("SATSubsumptionResolution::cnfForSubsumptionResolution");
  ASS(_L);
  ASS(_M);
  ASS(_solver->s.theory().empty());

  // -> b_ij implies a certain substitution is valid
  //    for each i, j : b_ij => (S(L_i) = M_j V S(L_i) = ~M_j)
  // These constraints are created in the fillMatches() function by filling the _bindingsManager
  Solver& solver = _solver->s;
  solver.theory().setBindings(_bindingsManager);

  // -> At least one negative polarity match exists
  //    b_11- V ... V b_1m- V ... V b_n1 V ... V b_nm-
  vvector<Match*> allMatches = _matchSet.getAllMatches();
  solver.constraint_start();
  for (Match* match : allMatches) {
    if (!match->_polarity) {
      solver.constraint_push_literal(match->_var);
    }
  }
  auto build = solver.constraint_end();
  solver.add_clause_unsafe(build);

  // -> Each L_i is matched by at least one M_j
  //    b_11 V ... V b_1k
  // /\ b_21 V ... V b_2k
  // /\ ...
  // /\ b_n1 V ... V b_nk
  for (unsigned i=0; i<_m; i++) {
    solver.constraint_start();
    for (Match* match : _matchSet.getIMatches(i)) {
      solver.constraint_push_literal(match->_var);
    }
    auto build = solver.constraint_end();
    solver.add_clause_unsafe(build);
  }

  // -> At most one M_j is matched by a negative polarity variable
  //    for each j : b_1j- V ... V b_nj- => ~b_ij', j' != j
  for(unsigned it1=0; it1<allMatches.size(); it1++) {
    Match* match1 = allMatches[it1];
    if(match1->_polarity) {
      continue;
    }
    for(unsigned it2=it1+1; it2<allMatches.size(); it2++) {
      Match* match2 = allMatches[it2];
      if (match2->_polarity
       || match1->_j == match2->_j) {
        continue;
      }
      solver.constraint_start();
      solver.constraint_push_literal(~match1->_var);
      solver.constraint_push_literal(~match1->_var);
      auto build = solver.constraint_end();
      solver.add_clause_unsafe(build);
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
Kernel::Clause *SATSubsumption::generateConclusion()
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
  #ifndef NDEBUG
  unsigned j = 0;
  // Check that there is only one negative polarity match to j inside the model
  for (subsat::Lit lit : _model) {
    if (lit.is_positive()) {
      Match *match = _matchSet.getMatchForVar(lit.var());
      // matches can be null if the variable is a c_j
      if (match && !match->_polarity) {
        if(j == 0) {
          j = match->_j;
        } else {
          ASS(j == match->_j);
        }
      }
    }
  }
  #endif
  unsigned toRemove = numeric_limits<unsigned>::max();
  // find the negative polarity match to j inside the model
  for (subsat::Lit lit : _model) {
    if (lit.is_positive()) {
      Match *match = _matchSet.getMatchForVar(lit.var());
      // matches can be null if the variable is a c_j
      if (match && !match->_polarity) {
        toRemove = match->_j;
        break;
      }
    }
  }
  ASS(toRemove != numeric_limits<unsigned>::max());
  // Create the conclusion clause
  Kernel::Clause *conclusion = new (_n - 1) Kernel::Clause(_n - 1, SimplifyingInference2(InferenceRule::SUBSUMPTION_RESOLUTION, _M, _L));
  unsigned k = 0;
  for (unsigned j = 0; j < _n; ++j) {
    if (j != toRemove) {
      conclusion->literals()[k] = _M->literals()[j];
      k++;
    }
  }
  ASS(k == _n - 1);
  //cerr << "Solution : " << conclusion->toString() << endl;
  return conclusion;
}

Kernel::Clause* SATSubsumption::checkSubsumptionResolution(Kernel::Clause *L, Kernel::Clause *M)
{
  CALL("SATSubsumption::checkSubsumptionResolution");
  //cerr << "checkSubsumptionResolution(" << L->toString() << ", " << M->toString() << ")" << endl;
  if(++_nSubsumptionResolutionCalls % 100000 == 0) {
    cerr << "check Subsumption Resolution : " << _nSubsumptionResolutionCalls << " calls" << endl;
  }
  if(M->length() < L->length()) {
    return nullptr;
  }
  setupProblem(L, M);

  // Checks for all the literal mapings and store them in a cache
  // nVar is the number of variables that are of the form b_ij
  if (!fillMatchesSR()) {
    return nullptr;
  }

  // First set up the clauses
  if (!cnfForSubsumptionResolution()) {
    return nullptr;
  }

  // Solve the SAT problem
  if(++_nSubsumptionResolutionSolverCalls % 10000 == 0) {
    cerr << "check Subsumption Resolution Solver : " << _nSubsumptionResolutionSolverCalls << " calls" << endl;
  }
  Solver& solver = _solver->s;
  if(solver.solve() != subsat::Result::Sat) {
    return nullptr;
  }
  _model.clear();
  solver.get_model(_model);

  // If the problem is SAT, then generate the conclusion clause
  return generateConclusion();
}
