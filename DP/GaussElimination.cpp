/*
 * File GaussElimination.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file GaussElimination.cpp
 * Implements class GaussElimination.
 */
#define GEDP DLADP

#include "GaussElimination.hpp"

namespace DP {

GaussElimination::GaussElimination(vector<LinearArithmeticDP::Constraint> &parsedLiterals)
{
  CALL("GaussElimination::GaussElimination");

  // Copy contents. TODO: check if we need to do this
  _rowsList = parsedLiterals;

  for (unsigned i = 0; i < _rowsList.size(); i++) {
    for (auto const &parameter : _rowsList[i].parameters) {
      _colLabelSet.insert(parameter.first);
    }
  }

  _status = UNKNOWN;
}

void GaussElimination::solve()
{
  CALL("GaussElimination::solve");
#if GEDP
  cout << "GaussElimination::solve" << endl;
  for (unsigned i = 0; i < _rowsList.size(); i++) {
    cout << _rowsList[i].toString() << endl
         << endl;
  }
#endif

  vector<LinearArithmeticDP::Constraint> newRowsList;

  vector<LinearArithmeticDP::Constraint> intermediateRowsList;
  intermediateRowsList.reserve(_rowsList.size());
  set<unsigned> rowsLeftIndex;
  for (unsigned i = 0; i < _rowsList.size(); i++) {
    intermediateRowsList.push_back(_rowsList[i]);
    rowsLeftIndex.insert(i);
  }

  for (auto const &colLabel : _colLabelSet) {
    set<unsigned> rowsIndexWithNonZero;
    for (auto const &rowIndex : rowsLeftIndex) {
      if (intermediateRowsList[rowIndex].parameters.find(colLabel) != intermediateRowsList[rowIndex].parameters.end() &&
          !intermediateRowsList[rowIndex].parameters[colLabel].isZero()) {
        rowsIndexWithNonZero.insert(rowIndex);
      }
    }

    if (rowsIndexWithNonZero.size() != 0) {
      set<unsigned>::iterator it = rowsIndexWithNonZero.begin();
      unsigned pivotIndex = *it;
      rowsLeftIndex.erase(pivotIndex);
      newRowsList.push_back(intermediateRowsList[pivotIndex]);
      it++;

      for (; it != rowsIndexWithNonZero.end(); it++) {
        unsigned rowIndex = *it;

        RationalConstantType multiplier = intermediateRowsList[rowIndex].parameters[colLabel] / intermediateRowsList[pivotIndex].parameters[colLabel];

        // subtract
        subtract(&intermediateRowsList[rowIndex], &intermediateRowsList[pivotIndex], multiplier);
      }
    }
  }

  // There are some leftover rows. Some are all zeros -> disregard. Others, check for satifiability
  for (auto const &rowIndex : rowsLeftIndex) {
    if (intermediateRowsList[rowIndex].parameters.size() == 0 && !intermediateRowsList[rowIndex].constant.isZero()) {
#if GEDP
      cout << "Unsatisfiable at row index " << rowIndex << ": ";
      cout << intermediateRowsList[rowIndex].toString() << endl;
#endif
      _inconsistentRowIndexes.push_back(rowIndex);
      _status = UNSATISFIABLE;
    }
  }

  if (_status == UNSATISFIABLE) {
    return;
  }

#if GEDP
  cout << "\nUpper Triangular Form" << endl;
  for (unsigned i = 0; i < newRowsList.size(); i++) {
    cout << newRowsList[i].toString() << endl
         << endl;
  }
#endif

  // At this point satisfiable. Possibly infinite solutions
  _rowsList = newRowsList;

  // if matrix is triangular form use back subsitution
  if (_rowsList.size() < _colLabelSet.size()) {
#if GEDP
    cout << "Satisfiable with infinite solutions as number of equations < number of unkowns." << endl;
#endif
    _status = SATISFIABLE_INFINITE;
    return;
  }

  _status = SATISFIABLE_ONE;
}

LinearArithmeticDP::Status GaussElimination::getStatus()
{
  if (_status == UNKNOWN) {
    solve();
  }

#if GEDP
  cout << "Status: " << (_status == UNSATISFIABLE ? "UNSAT" : "SAT") << endl;
#endif

  switch (_status) {
    case SATISFIABLE_ONE:
    case SATISFIABLE_INFINITE:
      return DecisionProcedure::SATISFIABLE;
      break;
    case UNSATISFIABLE:
      return DecisionProcedure::UNSATISFIABLE;
      break;
    default:
      return DecisionProcedure::UNKNOWN;
      break;
  }
}

// c1 = c1 - multiplier*c2
void GaussElimination::subtract(LinearArithmeticDP::Constraint *c1, LinearArithmeticDP::Constraint *c2, RationalConstantType multiplier)
{
  CALL("GaussElimination::subtract");
  for (auto const &c2parameter : c2->parameters) {
    if (c1->parameters.find(c2parameter.first) != c1->parameters.end()) {
      // found
      RationalConstantType result = c1->parameters[c2parameter.first] - (multiplier * c2parameter.second);
      if (result.isZero()) {
        c1->parameters.erase(c2parameter.first);
      }
      else {
        c1->parameters[c2parameter.first] = result;
      }
    }
    else {
      c1->parameters[c2parameter.first] = -multiplier * c2parameter.second;
    }
  }

  c1->constant = c1->constant - (multiplier * c2->constant);
}

vector<Literal *> GaussElimination::getModel()
{
  CALL("GaussElimination::getModel");
#if GEDP
  cout << "GaussElimination::getModel" << endl;
#endif
  if (_status == UNSATISFIABLE) {
    return vector<Literal *>();
  }

  if (_model.size() < 1) {
    setModel();
  }

  return _model;
}

void GaussElimination::setModel()
{
  map<unsigned, RationalConstantType> solutions;
  for (int i = _rowsList.size() - 1; i >= 0; i--) {
    map<unsigned, RationalConstantType>::iterator it = _rowsList[i].parameters.begin();
    it++;
    while (it != _rowsList[i].parameters.end()) {
      if (solutions.find(it->first) != solutions.end()) {
        _rowsList[i].constant = _rowsList[i].constant - (solutions[it->first] * _rowsList[i].parameters[it->first]);
        it = _rowsList[i].parameters.erase(it);
      }
      else {
        it++;
      }
    }

    if (_rowsList[i].parameters.size() == 1) {
      solutions[_rowsList[i].parameters.begin()->first] = _rowsList[i].constant / _rowsList[i].parameters.begin()->second;
    }
  }

  for (int i = _rowsList.size() - 1; i >= 0; i--) {
    TermList sort = env.signature->getFunction(_rowsList[i].parameters.begin()->first)->fnType()->result();
    if (sort == IntTraits::sort()) {
      // Turn all rationals to integers
      unsigned multiplier = 1;
      for (auto &parameter : _rowsList[i].parameters) {
        multiplier *= parameter.second.denominator().toInner();
      }
      multiplier *= _rowsList[i].constant.denominator().toInner();

      RationalConstantType multiplierRational = RationalConstantType(multiplier);
      for (auto &parameter : _rowsList[i].parameters) {
        parameter.second = multiplierRational * parameter.second;
      }
      _rowsList[i].constant = multiplierRational * _rowsList[i].constant;
    }

    map<unsigned, RationalConstantType>::iterator it = _rowsList[i].parameters.begin();
    Term *lhs = Term::createConstant(it->first);
    if (it->second != RationalConstantType(1)) {
       if(sort == IntTraits::sort()){
          Term *coef = theory->representConstant(it->second.numerator());
          lhs = Term::create2(env.signature->getInterpretingSymbol(Theory::INT_MULTIPLY), TermList(lhs), TermList(coef));
       } 
       else if(sort == RatTraits::sort()){
          Term *coef = theory->representConstant(it->second);
          lhs = Term::create2(env.signature->getInterpretingSymbol(Theory::RAT_MULTIPLY), TermList(lhs), TermList(coef));
       } 
       else if(sort == RealTraits::sort()){
          Term *coef = theory->representConstant(RealConstantType(it->second));
          lhs = Term::create2(env.signature->getInterpretingSymbol(Theory::REAL_MULTIPLY), TermList(lhs), TermList(coef));
       } 
       else{
         ASSERTION_VIOLATION;
       }
    }
    it++;

    for (; it != _rowsList[i].parameters.end(); it++) {
      Term *variable = Term::createConstant(it->first);
        if(sort == IntTraits::sort()){
          if (it->second != RationalConstantType(1)) {
            Term *coef = theory->representConstant(it->second.numerator());
            variable = Term::create2(env.signature->getInterpretingSymbol(Theory::INT_MULTIPLY), TermList(variable), TermList(coef));
          }
          lhs = Term::create2(env.signature->getInterpretingSymbol(Theory::INT_PLUS), TermList(lhs), TermList(variable));
        } 
        else if(sort == RatTraits::sort()){
          if (it->second != RationalConstantType(1)) {
            Term *coef = theory->representConstant(it->second);
            variable = Term::create2(env.signature->getInterpretingSymbol(Theory::RAT_MULTIPLY), TermList(variable), TermList(coef));
          }
          lhs = Term::create2(env.signature->getInterpretingSymbol(Theory::RAT_PLUS), TermList(lhs), TermList(variable));
        } 
        else if(sort == RealTraits::sort()){
          if (it->second != RationalConstantType(1)) {
            Term *coef = theory->representConstant(RealConstantType(it->second));
            variable = Term::create2(env.signature->getInterpretingSymbol(Theory::REAL_MULTIPLY), TermList(variable), TermList(coef));
          }
          lhs = Term::create2(env.signature->getInterpretingSymbol(Theory::REAL_PLUS), TermList(lhs), TermList(variable));
        } 
        else{
          ASSERTION_VIOLATION;
        }
    }

    Term *rhs;
    if(sort == IntTraits::sort()){
        rhs = theory->representConstant(IntegerConstantType(_rowsList[i].constant.numerator()));
    }
    else if(sort == RatTraits::sort()){
        rhs = theory->representConstant(_rowsList[i].constant);
    }
    else if(sort == RealTraits::sort()){
        rhs = theory->representConstant(RealConstantType(_rowsList[i].constant));
    } 
    else{
      ASSERTION_VIOLATION;
    }

    Literal *lit = Literal::createEquality(true, TermList(lhs), TermList(rhs), sort);
    #if GEDP
    cout << "New lit: " << lit->toString() << endl;
    #endif
    _model.push_back(lit);
  }
}

unsigned GaussElimination::getUnsatCoreCount()
{
  if (_status == SATISFIABLE_ONE || _status == SATISFIABLE_INFINITE) {
    return 0;
  }
  else {
    if (_unsatCores.size() < 1) {
      setUnsatCore();
    }

    return _unsatCores.size();
  }
}

set<unsigned> GaussElimination::getUnsatCore(unsigned coreIndex)
{
  if (_status == SATISFIABLE_ONE || _status == SATISFIABLE_INFINITE) {
    return set<unsigned>();
  }
  else {
    if (_unsatCores.size() < 1) {
      setUnsatCore();
    }

    if (coreIndex >= _unsatCores.size()) {
      return set<unsigned>();
    }

    return _unsatCores[coreIndex];
  }
}

bool GaussElimination::setInterference(LinearArithmeticDP::Constraint *row, set<unsigned> *interferenceSet)
{
  bool changed = false;
  for (auto const &parameter : row->parameters) {
    if (interferenceSet->insert(parameter.first).second) {
      changed = true;
    }
  }

  return changed;
}

bool GaussElimination::isInterfearing(LinearArithmeticDP::Constraint *row, set<unsigned> *interferenceSet)
{
  for (auto const &parameter : row->parameters) {
    if (interferenceSet->find(parameter.first) != interferenceSet->end()) {
      return true;
    }
  }

  return false;
}

bool GaussElimination::areInconsistentMultiples(LinearArithmeticDP::Constraint *row1, LinearArithmeticDP::Constraint *row2)
{
  // exactly same vars and have multiple coef, except for constant
  // Return true if inconsistant
  if (row1->parameters.size() != row2->parameters.size()) {
    return false;
  }

  map<unsigned, RationalConstantType>::iterator row1ParametersIt = row1->parameters.begin();
  map<unsigned, RationalConstantType>::iterator row2ParametersIt = row2->parameters.begin();

  if (row1ParametersIt->first != row2ParametersIt->first) {
    return false;
  }

  RationalConstantType multiplier = row2ParametersIt->second / row1ParametersIt->second;
  row1ParametersIt++;
  row2ParametersIt++;

  while (row1ParametersIt != row1->parameters.end()) {
    if (row1ParametersIt->first != row2ParametersIt->first) {
      return false;
    }

    if ((row1ParametersIt->second * multiplier) != row2ParametersIt->second) {
      return false;
    }

    row1ParametersIt++;
    row2ParametersIt++;
  }

  return (row1->constant * multiplier) != row2->constant;
}

void GaussElimination::setUnsatCore()
{
  vector<set<unsigned>> intermediateUnsatCores;
  intermediateUnsatCores.reserve(_inconsistentRowIndexes.size());
  for (unsigned i = 0; i < _inconsistentRowIndexes.size(); i++) {
    unsigned inconsistentRowIndex = _inconsistentRowIndexes[i];

    set<unsigned> interferenceSet;
    bool interferenceSetHasChanged;
    interferenceSetHasChanged = true;
    setInterference(&_rowsList[inconsistentRowIndex], &interferenceSet);

    set<unsigned> unsatCore;
    unsatCore.insert(inconsistentRowIndex);

    set<unsigned> rowsLeftIndexes;
    for (unsigned j = 0; j < inconsistentRowIndex; j++) {
      rowsLeftIndexes.insert(j);
    }

    for (unsigned j = inconsistentRowIndex + 1; j < _rowsList.size(); j++) {
      rowsLeftIndexes.insert(j);
    }

    while (interferenceSetHasChanged) {
      interferenceSetHasChanged = false;
      set<unsigned>::iterator it = rowsLeftIndexes.begin();
      while (it != rowsLeftIndexes.end()) {
        unsigned rowIndex = *it;
        if (isInterfearing(&_rowsList[rowIndex], &interferenceSet)) {
          interferenceSetHasChanged |= setInterference(&_rowsList[rowIndex], &interferenceSet);
          unsatCore.insert(rowIndex);
          it = rowsLeftIndexes.erase(it);
        }
        else {
          ++it;
        }
      }
    }

    intermediateUnsatCores.push_back(unsatCore);
  }

  // Check for overlap and parallel.
  for (unsigned i = 0; i < intermediateUnsatCores.size(); i++) {
    set<unsigned> intermediateUnsatCore = intermediateUnsatCores[i];
    unsigned inconsistentRowIndex = _inconsistentRowIndexes[i];

    set<unsigned> unsatCore;
    unsatCore.insert(inconsistentRowIndex);

    set<unsigned>::iterator it = intermediateUnsatCore.begin();
    for (; *it != inconsistentRowIndex; it++) {
      unsigned rowIndex = *it;
      if (areInconsistentMultiples(&_rowsList[inconsistentRowIndex], &_rowsList[rowIndex])) {
        unsatCore.insert(rowIndex);
      }
    }
    it++;
    for (; it != intermediateUnsatCore.end(); it++) {
      unsigned rowIndex = *it;
      if (areInconsistentMultiples(&_rowsList[inconsistentRowIndex], &_rowsList[rowIndex])) {
        unsatCore.insert(rowIndex);
      }
    }

    set<unsigned> core = (unsatCore.size() > 1) ? unsatCore : intermediateUnsatCore;
    if (find(_unsatCores.begin(), _unsatCores.end(), core) == _unsatCores.end()) {
      _unsatCores.push_back(core);
    }
  }
}

GaussElimination::~GaussElimination()
{
  CALL("GaussElimination::~GaussElimination");
}
} // namespace DP
