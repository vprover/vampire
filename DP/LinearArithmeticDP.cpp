/*
 * File LinearArithmeticDP.cpp.
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
 * @file LinearArithmeticDP.cpp
 * Implements class LinearArithmeticDP.
 */

#define DLADP 1

#include <sstream>
#include <iostream>
#include <set>

#include "LinearArithmeticDP.hpp"
#include "GaussElimination.hpp"

#include "Lib/Environment.hpp"

#include "Kernel/TermIterators.hpp"
#include "Kernel/Theory.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"

namespace DP {

LinearArithmeticDP::LinearArithmeticDP()
{
  CALL("LinearArithmeticDP::LinearArithmeticDP");
}

void LinearArithmeticDP::reset()
{
  CALL("LinearArithmeticDP::reset");
#if DLADP
  cout << "#####################RESET#####################\n\n"
       << endl;
#endif
  if (solverDP != NULL) {
    delete solverDP;
    solverDP = NULL;
  }
  solver = Undefined;
  rowsVector.clear();
  colLabelSet.clear();
}

/**
 * Add literals based on their structure
 * - if non-ground then ignore
 * - if contains symbols that are not +, -, =, or <, numbers, or numeric constants then ignore
 *
 */
void LinearArithmeticDP::addLiterals(LiteralIterator lits, bool onlyEqualites)
{
  CALL("LinearArithmeticDP::addLiterals");

  if (onlyEqualites) {
    solver = LinearArithmeticDP::GaussElimination;
  }
  else {
    solver = LinearArithmeticDP::Simplex;
  }
  // for now override dues to issues with onlyEqualities
  solver = LinearArithmeticDP::GaussElimination;

#if DLADP
  cout << ">> addLiterals" << endl;
#endif
  while (lits.hasNext()) {
    Literal *l = lits.next();
    if (!l->ground()) {
      //for now we ignore non-ground literals
      continue;
    }
#if DLADP
    cout << "Check " << l->toString() << endl;
#endif
    if (!theory->isInterpretedPredicate(l))
      continue;
    SubtermIterator sit(l);
    bool skip = false;
    while (sit.hasNext()) {
      // As l is ground we know that this term exists e.g. it's not a variable
      Term *st = sit.next().term();
      unsigned fun = st->functor();

      // Checking if function is a constant and is a numeric constants
      if (env.signature->functionArity(fun) == 0 && Sorts::isNumericSort(SortHelper::getResultSort(st)))
        continue;
      if (theory->isInterpretedNumber(st))
        continue;
      if (theory->isInterpretedFunction(fun)) {
        Interpretation interp = theory->interpretFunction(fun);
        if (theory->isLinearOperation(interp))
          continue;

        // We're still linear if this is a multiplication by a number
        if (interp == Interpretation::INT_MULTIPLY || interp == Interpretation::RAT_MULTIPLY || interp == Interpretation::REAL_MULTIPLY) {
          // Again, have to be terms as there are no variables
          Term *left = st->nthArgument(0)->term();
          Term *right = st->nthArgument(1)->term();
          if (theory->isInterpretedNumber(left) || theory->isInterpretedNumber(right))
            continue;
        }
      }
      skip = true;
      break;
    }
    if (skip)
      continue;
    //cout << "Only Equalities: " << onlyEqualites << "l->isEquality(): " << l->isEquality() << "l->isPositive(): " << l->isPositive() << endl;
    //if (!onlyEqualites || (l->isEquality() && l->isPositive())) {
    //  addLiteral(l);
    //}
    if (l->isEquality() && l->isPositive())
      addLiteral(l);
  }
}

void LinearArithmeticDP::addLiteral(Literal *lit)
{
  CALL("LinearArithmeticDP::addLiteral");

#if DLADP
  cout << "###########Adding " << lit->toString() << endl;
#endif

  Term *leftHandSide = lit->nthArgument(0)->term();
  Term *rightHandSide = lit->nthArgument(1)->term();

  try {
    ParameterDataContainer parData;
    toParams(leftHandSide, RationalConstantType(1, 1), &parData);
    toParams(rightHandSide, RationalConstantType(-1, 1), &parData);

    List<Parameter> *row = 0;
    List<Parameter>::push(Parameter(UINT_MAX, -parData.constant), row);

    map<unsigned, RationalConstantType>::reverse_iterator it = parData.parameters.rbegin();
    while (it != parData.parameters.rend()) {
      List<Parameter>::push(Parameter(it->first, it->second), row);
      colLabelSet.insert(it->first);
      it++;
    }
    rowsVector.push_back(row);
  }
  // Skipping
  catch (invalid_argument e) {
  }
}

RationalConstantType toRational(Term *term)
{
  unsigned func = term->functor();
  Signature::Symbol *sym = env.signature->getFunction(func);
  if (sym->integerConstant())
    return RationalConstantType(sym->integerValue());

  if (sym->rationalConstant())
    return sym->rationalValue();

  if (sym->realConstant())
    return sym->realValue();

  return RationalConstantType(1, 1);
}

void LinearArithmeticDP::toParams(Term *term, RationalConstantType coef, LinearArithmeticDP::ParameterDataContainer *parData)
{
  CALL("LinearArithmeticDP::toParams");
  unsigned arity = term->arity();
  // base case
  if (arity == 0) {
    unsigned fun = term->functor();
    // Either got a number of a constant or paramerter
    if (theory->isInterpretedNumber(term)) {
      parData->constant = parData->constant + (coef * toRational(term));
    }
    else {
      // If parameter insert or update
      if (parData->parameters.find(fun) == parData->parameters.end()) {
        parData->parameters[fun] = coef;
      }
      else {
        parData->parameters[fun] = parData->parameters[fun] + coef;
      }
    }
  }
  // unary minus
  else if (arity == 1) {
    toParams(term->nthArgument(0)->term(), -coef, parData);
  }
  else {
    // check if you have ADD or a MULT
    unsigned fun = term->functor();
    Interpretation interp = theory->interpretFunction(fun);
    // Multiply
    if (interp == Interpretation::INT_MULTIPLY || interp == Interpretation::RAT_MULTIPLY || interp == Interpretation::REAL_MULTIPLY) {
      if (theory->isInterpretedNumber(term->nthArgument(0)->term())) {
        toParams(term->nthArgument(1)->term(), coef * toRational(term->nthArgument(0)->term()), parData);
      }
      else {
        toParams(term->nthArgument(0)->term(), coef * toRational(term->nthArgument(1)->term()), parData);
      }
    }
    // Adition
    else if (interp == Interpretation::INT_PLUS || interp == Interpretation::RAT_PLUS || interp == Interpretation::REAL_PLUS) {
      toParams(term->nthArgument(0)->term(), coef, parData);
      toParams(term->nthArgument(1)->term(), coef, parData);
    }
    else {
      throw invalid_argument("Anything other than addition or multiplication is not permeated");
    }
  }
}

DecisionProcedure::Status LinearArithmeticDP::getStatus(bool retrieveMultipleCores)
{
  CALL("LinearArithmeticDP::getStatus");
#if DLADP
  cout << "##############Solve############" << endl;
#endif
  if (rowsVector.size() < 1)
    return DecisionProcedure::SATISFIABLE;
  switch (solver) {
    case GaussElimination: {
      solverDP = new DP::GaussElimination(rowsVector, colLabelSet);
      return solverDP->getStatus();
    }
    case Simplex: {
      return DecisionProcedure::SATISFIABLE;
    }
    default: {
      return DecisionProcedure::UNKNOWN;
    }
  }
}

void LinearArithmeticDP::getModel(LiteralStack &model)
{
  CALL("LinearArithmeticDP::getModel");
#if DLADP
  cout << "LinearArithmeticDP::getModel" << endl;
#endif
  if (solverDP != NULL)
    solverDP->getModel(model);
}

} // namespace DP
