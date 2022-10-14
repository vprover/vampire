#include "SATSubsumptionResolution.hpp"
#include "Kernel/Matcher.hpp"
#include "Debug/RuntimeStatistics.hpp"
#include "Util.hpp"
#include <iostream>

using namespace Indexing;
using namespace Kernel;
using namespace SMTSubsumption;

#define SAT_SR_IMPL 1

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
SATSubsumption::MatchSet::MatchSet(unsigned nBaseLits, unsigned nInstanceLits)
    : _i_matches(nBaseLits),
      _j_matches(nInstanceLits),
      _i_matcheState(nBaseLits / 4 + 1, 0),
      _j_matcheState(nInstanceLits / 4 + 1, 0),
      _nBaseLits(nBaseLits),
      _nInstanceLits(nInstanceLits),
      _varToMatch(),
      _nUsedMatches(0),
      _nAllocatedMatches(1),
      _allocatedMatches(nullptr)
{
  ASS(nBaseLits > 0);
  _allocatedMatches = (Match**) malloc(_nAllocatedMatches * sizeof(Match*));
  _allocatedMatches[0] = (Match*) malloc(sizeof(Match));
}

SATSubsumption::MatchSet::~MatchSet()
{
  for (unsigned i = 1; i < _nUsedMatches; i*=2) {
    free(_allocatedMatches[i-1]);
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

void SATSubsumption::MatchSet::resize(unsigned nBaseLits, unsigned nInstanceLits)
{
  ASS(nBaseLits > 0);
  ASS(nInstanceLits > 0);
  ASS(nBaseLits >= _nBaseLits);
  ASS(nInstanceLits >= _nInstanceLits);
  if (nBaseLits > _i_matches.size()) {
    _i_matches.resize(nBaseLits);
  }
  if (nInstanceLits > _i_matches.size()) {
    _j_matches.resize(nInstanceLits);
  }
  _nBaseLits = nBaseLits;
  _nInstanceLits = nInstanceLits;

  if (nBaseLits / 4 + 1 > _i_matcheState.size()) {
    _i_matcheState.resize(nBaseLits / 4 + 1, 0);
  }
  if (nInstanceLits / 4 + 1 > _j_matcheState.size()) {
    _j_matcheState.resize(nInstanceLits / 4 + 1, 0);
  }
}

void SATSubsumption::MatchSet::addMatch(SATSubsumption::Match *match)
{
  unsigned i = match->_baseLitIndex;
  unsigned j = match->_instanceLitIndex;
  ASS(i < _nBaseLits);
  ASS(j < _nInstanceLits);
  _i_matches[i].push_back(match);
  _j_matches[j].push_back(match);
  unsigned index = match->_satVar.index();
  if (_varToMatch.size() <= index) {
    _varToMatch.resize(index * 2 + 1);
  }
  _varToMatch[index] = match;
  // update the match state
  // the wizardry is explained in the header file
  if (match->_isPositive) {
    _i_matcheState[i / 4] |= 1 << (2 * (i % 4));
    _j_matcheState[j / 4] |= 1 << (2 * (j % 4));
  } else {
    _i_matcheState[i / 4] |= 1 << (2 * (i % 4) + 1);
    _j_matcheState[j / 4] |= 1 << (2 * (j % 4) + 1);
  }
}

vvector<SATSubsumption::Match *> &SATSubsumption::MatchSet::getMatchesForBaseLit(unsigned baseLitIndex)
{
  ASS(baseLitIndex < _nBaseLits);
  return _i_matches[baseLitIndex];
}

vvector<SATSubsumption::Match *> &SATSubsumption::MatchSet::getMatchesForInstanceLit(unsigned instanceLitIndex)
{
  ASS(instanceLitIndex < _nInstanceLits);
  return _j_matches[instanceLitIndex];
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

bool SATSubsumption::MatchSet::hasPositiveMatchForBaseLit(unsigned i) {
  // the wizardry is explained in the header file
  return (_i_matcheState[i / 4] & (1 << (2 * (i % 4)))) != 0;
}

bool SATSubsumption::MatchSet::hasNegativeMatchForBaseLit(unsigned i) {
  // the wizardry is explained in the header file
  return (_i_matcheState[i / 4] & (2 << (2 * (i % 4)))) != 0;
}

bool SATSubsumption::MatchSet::hasPositiveMatchForInstanceLit(unsigned j) {
  // the wizardry is explained in the header file
  return (_j_matcheState[j / 4] & (1 << (2 * (j % 4)))) != 0;
}

bool SATSubsumption::MatchSet::hasNegativeMatchForInstanceLit(unsigned j) {
  // the wizardry is explained in the header file
  return (_j_matcheState[j / 4] & (2 << (2 * (j % 4)))) != 0;
}

void SATSubsumption::MatchSet::clear()
{
  for (unsigned i = 0; i < _nBaseLits; i++) {
    _i_matches[i].clear();
  }
  for (unsigned j = 0; j < _nInstanceLits; j++) {
    _j_matches[j].clear();
  }
  _nUsedMatches = 0;
  _varToMatch.clear();

  fill(_i_matcheState.begin(), _i_matcheState.end(), 0);
  fill(_j_matcheState.begin(), _j_matcheState.end(), 0);
}

/****************************************************************************/
/*                    SATSubsumption::SATSubsumption                        */
/****************************************************************************/

SATSubsumption::SATSubsumption() :
  _base(nullptr),
  _instance(nullptr),
  _nBaseLits(0),
  _nInstanceLits(0),
  _solver(new SolverWrapper()),
  _bindingsManager(new BindingsManager()),
  _atMostOneVars(),
  _matchSet(1, 1),
  _model()
{
  // nothing to do
}

SATSubsumption::~SATSubsumption()
{
  delete _bindingsManager;
}

void SATSubsumption::addBinding(BindingsManager::Binder *binder, unsigned varNumber, unsigned i, unsigned j, bool isPositive)
{
  subsat::Var satVar = _solver->s.new_variable(varNumber);
  Match *match = _matchSet.allocateMatch();
  match->_baseLitIndex = i;
  match->_instanceLitIndex = j;
  match->_satVar = satVar;
  match->_isPositive = isPositive;
  _matchSet.addMatch(match);
  _bindingsManager->commit_bindings(*binder, satVar, j, j);
  cout << match->_satVar << " : " << "(" << _base->literals()[i]->toString() << "  ->  " << _instance->literals()[j]->toString() << ")" << endl;

}

unsigned SATSubsumption::fillMatches()
{
  CALL("SATSubsumption::fillMatches");
  ASS(_base);
  ASS(_instance);
  ASS(_nBaseLits > 0);
  ASS(_nInstanceLits > 0);
  ASS(_matchSet._nBaseLits == _nBaseLits);
  ASS(_matchSet._nInstanceLits == _nInstanceLits);
  ASS(_bindingsManager);

  _solver->s.clear();

  _matchSet.resize(_nBaseLits, _nInstanceLits);
  _matchSet.clear();

  // number of matches found - is equal to the number of variables in the SAT solver
  unsigned nMatches = 0;
  // used ot check that the SR is even possible
  // the intersection represents the set of M_j that have been matched only negatively by some L_i
  vvector<unsigned> intersection;

  // for some L_i, stores the set of M_j that have been negatively matched by L_i
  vvector<unsigned> negativeMatches = vvector<unsigned>(_nInstanceLits);

  bool hasNegativeMatch = false;

  unsigned lastHeader = numeric_limits<unsigned>::max();
  for (unsigned i = 0; i < _nBaseLits; ++i)
  {
    Literal* baseLit = _base->literals()[i];
    Literal* baseLitNeg = Literal::complementaryLiteral(baseLit);
    bool foundPositiveMatch = false;

    negativeMatches.clear();
    for (unsigned j = 0; j < _nInstanceLits; ++j)
    {
      Literal* instLit = _instance->literals()[j];
      // very fast check that can discard most substitutions
      if (!Literal::headersMatch(baseLit, instLit, false)
       && !Literal::headersMatch(baseLitNeg, instLit, false)) {
        continue;
      }

      if(baseLit->polarity() == instLit->polarity())
      {
        // Search for positive literal matches
        {
          auto binder = _bindingsManager->start_binder();
          if (baseLit->arity() == 0 || MatchingUtils::matchArgs(baseLit, instLit, binder)) {
            addBinding(&binder, ++nMatches, i, j, true);
            foundPositiveMatch = true;
          }
        }
        // In case of commutative predicates such as equality, we also need to check the other way around
        if (baseLit->commutative()) {
          auto binder = _bindingsManager->start_binder();
          if (MatchingUtils::matchReversedArgs(baseLit, instLit, binder)) {
            addBinding(&binder, ++nMatches, i, j, true);
            foundPositiveMatch = true;
          }
        }
      } // end of positive literal match
      else {
        // Search for negative literal matches
        {
          auto binder = _bindingsManager->start_binder();
          if (baseLitNeg->arity() == 0 || MatchingUtils::matchArgs(baseLitNeg, instLit, binder)) {
            addBinding(&binder, ++nMatches, i, j, false);
            negativeMatches.push_back(j);
            hasNegativeMatch = true;
          }
        }
        // In case of commutative predicates such as equality, we also need to check the other way around
        if (baseLitNeg->commutative()) {
          auto binder = _bindingsManager->start_binder();
          if (MatchingUtils::matchReversedArgs(baseLitNeg, instLit, binder)) {
            addBinding(&binder, ++nMatches, i, j, false);
            if (negativeMatches[negativeMatches.size() - 1] != j) {
              negativeMatches.push_back(j);
              hasNegativeMatch = true;
            }
          }
        }
      } // end of negative literal matches
    } // for (unsigned j = 0; j < _nInstanceLits; ++j)

    if (!foundPositiveMatch) {
      // If the headers are different, then the SR is impossible
      if (lastHeader == numeric_limits<unsigned>::max()) {
        lastHeader = baseLit->header();
        // set up the first intersection
        if (negativeMatches.empty()) {
          return 0;
        }
        intersection = vvector<unsigned>(negativeMatches);
        continue;
      } else if (lastHeader != baseLit->header()) {
        return 0;
      }
      if (!_matchSet.hasNegativeMatchForBaseLit(i)) {
        // If there is no negative match for L_i, then the SR is impossible
        // Would be checked by next condition, but this one is faster
        return 0;
      }

      intersect(intersection, negativeMatches);
      if (intersection.empty()) {
        // It is impossible to find a SR because some L_i have no possible match
        return 0;
      }
    } // if (!foundPositiveMatch)
  } // for (unsigned i = 0; i < _nBaseLits; ++i)

  if (!hasNegativeMatch) {
    // If there are no negative matches, then the SR is not possible
    return 0;
  }

  return nMatches;
} // SATSubsumption::fillMatches()

#if SAT_SR_IMPL == 1
/**
 * This function assumes that the subsumption problem has been set up.
 * Subsumption resolution assumes that both the base and the instance are not tautologies.
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
 *    c_1 V c_2 V ... V c_k
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
bool SATSubsumption::setupSubsumptionResolution(Kernel::Clause *base, Kernel::Clause *instance)
{
  CALL("SATSubsumptionResolution::setupSubsumptionResolution");
  // Checks for all the literal mapings and store them in a cache
  // nBVar is the number of variables that are of the form b_ij
  unsigned nBVar = fillMatches();
  if (nBVar == 0) {
    return false;
  }

  // -> b_ij implies a certain substitution is valid
  //    for each i, j : b_ij => (S(L_i) = M_j V S(L_i) = ~M_j)
  // These constraints are created in the fillMatches() function by filling the _bindingsManager
  Solver& solver = _solver->s;
  ASS(solver.theory().empty());
  solver.theory().setBindings(_bindingsManager);

  // Set up the _atMostOneVars vectors to store the c_j
  if(_atMostOneVars.capacity() < _nInstanceLits) {
    _atMostOneVars.reserve(_nInstanceLits);
  }
  _atMostOneVars.clear();
  // Create the set of clauses

  // -> At least one negative polarity match exists
  //    c_1 V c_2 V ... V c_k
  cout << "----- c_1 V c_2 V ... V c_k" << endl;
  solver.constraint_start();
  string s = "";
  for (unsigned j = 0; j < _nInstanceLits; ++j) {
    // Do not add useless variables in the solver
    // It would compromise correctness since a c_j without binding coud be true and satisfy c_1 V ... V c_k without making any other clause false.
    if(_matchSet.hasNegativeMatchForInstanceLit(j)) {
      subsat::Var c_j = solver.new_variable(++nBVar);
      _atMostOneVars.push_back(pair<unsigned, subsat::Var>(j, c_j));
      s += "c" + to_string(c_j.index()) + " V ";
      solver.constraint_push_literal(c_j);
    }
  }
  // remove the last " V "
  s = s.substr(0, s.size() - 3);
  cout << s << endl;
  auto build = solver.constraint_end();
  // add the c_1 V ... V c_k clause
  solver.add_clause_unsafe(build);
  // -> At most one M_j is matched by a negative polarity variable
  //    At most one c_j is true (embeded in the sat solver)
  solver.add_atmostone_constraint_unsafe(build);
  // -> Each L_i is matched by at least one M_j
  //    b_11 V ... V b_1k
  // /\ b_21 V ... V b_2k
  // /\ ...
  // /\ b_n1 V ... V b_nk
  cout << "----- b_11 V ... V b_1k /\\ ... /\\ b_n1 V ... V b_nk" << endl;
  for (unsigned i = 0; i < _nBaseLits; ++i) {
    solver.constraint_start();
    vvector<Match*> &matches = _matchSet.getMatchesForBaseLit(i);
    for (Match *match : matches) {
      cout << match->_satVar;
      if (match != matches.back()) {
        cout << " V ";
      }
      solver.constraint_push_literal(match->_satVar);
    }
    cout << endl;
    auto build = solver.constraint_end();
    solver.add_clause_unsafe(build);
  }

  // -> c_j is true if and only if there is a negative polarity match b_ij-
  //    for each j : c_j <=> b_ij- for some i
  //    for each j :(~c_j V b_1j- V ... V b_nj-)
  //            /\ (c_j V ~b_1j-) /\ ... /\ (c_j V ~b_nj-)
  cout << "----- c_j <=> b_ij-" << endl;
  for (auto &pair : _atMostOneVars) {
    unsigned j = pair.first;
    vvector<Match*> &matches = _matchSet.getMatchesForInstanceLit(j);
    subsat::Var c_j = pair.second;
    solver.constraint_start();
    //   (~c_j V b_1j- V ... V b_nj-)
    cout << "----- (~c_j V b_1j- V ... V b_nj-)" << endl;
    cout << ~c_j;
    solver.constraint_push_literal(~c_j);
    for (Match* match : matches) {
      if (!match->_isPositive) {
        cout << " V " << match->_satVar;
        solver.constraint_push_literal(match->_satVar);
      }
    }
    cout << endl;
    auto build = solver.constraint_end();
    solver.add_clause_unsafe(build);
    //   (c_j V ~b_1j-) /\ ... /\ (c_j V ~b_nj-)
    cout << "----- (c_j V ~b_1j-) /\\ ... /\\ (c_j V ~b_nj-)" << endl;
    for (Match* match : matches) {
      if (!match->_isPositive) {
        solver.constraint_start();
        cout << c_j << " V " << ~match->_satVar << endl;
        solver.constraint_push_literal(c_j);
        solver.constraint_push_literal(~match->_satVar);
        auto build = solver.constraint_end();
        solver.add_clause_unsafe(build);
      }
    }
    cout << endl;
  }
  return true;
} // setupSubsumptionResolution

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
  ASS(_base);
  ASS(_instance);
  ASS(_nBaseLits > 0);
  ASS(_nInstanceLits > 0);
  ASS(_matchSet._nBaseLits == _nBaseLits);
  ASS(_matchSet._nInstanceLits == _nInstanceLits);
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
      if (match && !match->_isPositive) {
        if(j == 0) {
          j = match->_instanceLitIndex;
        } else {
          ASS(j == match->_instanceLitIndex);
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
      if (match && !match->_isPositive) {
        toRemove = match->_instanceLitIndex;
        break;
      }
    }
  }
  ASS(toRemove != numeric_limits<unsigned>::max());
  // Create the conclusion clause
  Kernel::Clause *conclusion = new (_nInstanceLits - 1) Kernel::Clause(_nInstanceLits - 1, SimplifyingInference2(InferenceRule::SUBSUMPTION_RESOLUTION, _instance, _base));
  unsigned k = 0;
  for (unsigned j = 0; j < _nInstanceLits; ++j) {
    if (j != toRemove) {
      conclusion->literals()[k] = _instance->literals()[j];
      k++;
    }
  }
  ASS(k == _nInstanceLits - 1);
  return conclusion;
}

Kernel::Clause* SATSubsumption::checkSubsumptionResolution(Kernel::Clause *base, Kernel::Clause *instance)
{
  cout << "----------------- CHECK SUBSUMPTION RESOLUTION -----------------" << endl;
  CALL("SATSubsumptionResolution::checkSubsumptionResolution");
  // Set up the problem
  _base = base;
  _instance = instance;
  _nBaseLits = base->length();
  _nInstanceLits = instance->length();
  if(_bindingsManager) {
    delete _bindingsManager;
  }
  _bindingsManager = new BindingsManager();

  _matchSet.clear();
  _matchSet.resize(_nBaseLits, _nInstanceLits);


  // First set up the clauses
  if (!setupSubsumptionResolution(base, instance)) {
    return nullptr;
  }

  // Solve the SAT problem
  Solver& solver = _solver->s;
  cout << "Solving" << endl;
  if(solver.solve() != subsat::Result::Sat) {
    cout << "Unsat" << endl;
    return nullptr;
  }
  _model.clear();
  solver.get_model(_model);

  // If the problem is SAT, then generate the conclusion clause
  return generateConclusion();
}

#else // SAT_SR_IMPL == 2
/**
 * This function assumes that the subsumption problem has been set up.
 */
bool SATSubsumption::setupSubsumptionResolution(Kernel::Clause *base)
{
  CALL("SATSubsumptionResolution::setupSubsumptionResolution");

} // setupSubsumptionResolution

Kernel::Clause *SATSubsumption::getSubsumptionResolutionConclusion(Kernel::Clause *base)
{
  CALL("SATSubsumptionResolution::getSubsumptionResolutionConclusion");
}

bool SATSubsumption::checkSubsumptionResolution(Kernel::Clause *base, Kernel::Clause *instance, Kernel::Clause *conclusion)
{
  CALL("SATSubsumptionResolution::checkSubsumptionResolution");
}
#endif
