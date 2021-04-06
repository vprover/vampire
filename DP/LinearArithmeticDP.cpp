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

#include <sstream>
#include <iostream>
#include <set>

#include "LinearArithmeticDP.hpp"
#include "GaussElimination.hpp"
#include "SimplexDP.hpp"

#include "Lib/Environment.hpp"

#include "Kernel/TermIterators.hpp"
#include "Kernel/Theory.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"

namespace DP {

LinearArithmeticDP::LinearArithmeticDP()
{
  CALL("LinearArithmeticDP::LinearArithmeticDP");

#if UseCache
  cache.solverType = Options::LinearArithmeticDP::OFF;
  cache.solverDP = NULL;
#endif
}

LinearArithmeticDP::~LinearArithmeticDP()
{
  CALL("LinearArithmeticDP::~LinearArithmeticDP");
  reset();

#if UseCache
  if (cache.solverDP != NULL) {
    delete cache.solverDP;
  }
#endif
}

void LinearArithmeticDP::reset()
{
  CALL("LinearArithmeticDP::reset");
#if DLADP
  cout << "LinearArithmeticDP::reset\n"
       << endl;
#endif

#if UseCache
  cache.solverType = env.options->ladp();
  cache.solverDP = solverDP;
  cache.constraints.clear();
  cache.constraints.reserve(parsedLiterals.size());
  for (unsigned i = 0; i < parsedLiterals.size(); i++) {
    cache.constraints[i] = parsedLiterals[i].parent;
  }

  solverDP = NULL;
  parsedLiterals.clear();
  return;
#endif

  parsedLiterals.clear();
  if (solverDP != NULL) {
    delete solverDP;
    solverDP = NULL;
  }
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

#if DLADP
  cout << "LinearArithmeticDP::addLiterals" << endl;
#endif
  while (lits.hasNext()) {
    Literal *l = lits.next();
    if (!l->ground()) {
      //for now we ignore non-ground literals
      continue;
    }
#if DLADP
    //cout << "Check " << l->toString() << endl;
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

    if ((env.options->ladp() == Options::LinearArithmeticDP::GE && l->isEquality() && l->isPositive()) || (env.options->ladp() == Options::LinearArithmeticDP::SIMPLEX)) {
      addLiteral(l);
    }
  }
}

void LinearArithmeticDP::addLiteral(Literal *lit)
{
  CALL("LinearArithmeticDP::addLiteral");

#if DLADP
  cout << "LinearArithmeticDP::addLiteral: " << lit->toString() << endl;
#endif

#if UseCache
  if (addConstraintIfInCache(lit)) {
    return;
  }
#endif
  // before creating solver check cache
  try {
    Term *leftHandSide = lit->nthArgument(0)->term();
    Term *rightHandSide = lit->nthArgument(1)->term();

    // Setting predicate
    unsigned fun = lit->functor();
    Interpretation predicate = theory->interpretPredicate(fun);
    RationalConstantType coef;

    Interpretation finalPredicate;
    switch (predicate) {
      case Interpretation::EQUAL: {
        finalPredicate = Interpretation::EQUAL;
        coef = RationalConstantType(1);
      } break;
      case Interpretation::INT_LESS:
      case Interpretation::RAT_LESS:
      case Interpretation::REAL_LESS: {
        finalPredicate = lit->isPositive() ? Interpretation::RAT_LESS : Interpretation::RAT_LESS_EQUAL;
        coef = lit->isPositive() ? RationalConstantType(1) : RationalConstantType(-1);
      } break;
      case Interpretation::INT_GREATER:
      case Interpretation::RAT_GREATER:
      case Interpretation::REAL_GREATER: {
        finalPredicate = lit->isPositive() ? Interpretation::RAT_LESS : Interpretation::RAT_LESS_EQUAL;
        coef = lit->isPositive() ? RationalConstantType(-1) : RationalConstantType(1);
      } break;
      default:
        return;
    }

    if (finalPredicate == Interpretation::EQUAL && env.options->ladp() == Options::LinearArithmeticDP::SIMPLEX) {
      Constraint parDataLessEqual;
      toParams(leftHandSide, RationalConstantType(1), &parDataLessEqual);
      toParams(rightHandSide, RationalConstantType(-1), &parDataLessEqual);
      parDataLessEqual.predicate = Interpretation::RAT_LESS_EQUAL;
      parDataLessEqual.parent = lit;
      parsedLiterals.push_back(parDataLessEqual);

      Constraint parDataGreaterEqual;
      toParams(leftHandSide, RationalConstantType(-1), &parDataGreaterEqual);
      toParams(rightHandSide, RationalConstantType(1), &parDataGreaterEqual);
      parDataGreaterEqual.predicate = Interpretation::RAT_LESS_EQUAL;
      parDataGreaterEqual.parent = lit;
      parsedLiterals.push_back(parDataGreaterEqual);
#if UseCache
      cache.parsedLiterals[lit] = parDataLessEqual;
#endif

#if DLADP
      cout << "Equals converted to >= and <=" << endl;
      cout << parDataLessEqual.toString() << endl;
      cout << parDataGreaterEqual.toString() << endl;
#endif
    }
    else {
      Constraint parData;
      toParams(leftHandSide, coef, &parData);
      toParams(rightHandSide, -coef, &parData);
      parData.predicate = finalPredicate;
      parData.parent = lit;
      parsedLiterals.push_back(parData);
#if UseCache
      cache.parsedLiterals[lit] = parData;
#endif
#if DLADP
      cout << parData.toString() << endl;
#endif
    }
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

void LinearArithmeticDP::toParams(Term *term, RationalConstantType coef, LinearArithmeticDP::Constraint *parData)
{
  CALL("LinearArithmeticDP::toParams");
  unsigned arity = term->arity();
  // base case
  if (arity == 0) {
    unsigned fun = term->functor();
    // Either got a number of a constant or paramerter
    if (theory->isInterpretedNumber(term)) {
      parData->constant = parData->constant + (-coef * toRational(term));
    }
    else {
      if (!coef.isZero()) {
        // If parameter insert or update
        if (parData->parameters.find(fun) == parData->parameters.end()) {
          parData->parameters[fun] = coef;
        }
        else {
          parData->parameters[fun] = parData->parameters[fun] + coef;
        }
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
  cout << "LinearArithmeticDP::getStatus" << endl;
#endif
  if (parsedLiterals.size() < 1)
    return DecisionProcedure::SATISFIABLE;

#if UseCache
  if (addSolverDPIfInCache()) {
    return solverDP->getStatus();
  }
#endif

  switch (env.options->ladp()) {
    case Options::LinearArithmeticDP::GE: {
      solverDP = new DP::GaussElimination(parsedLiterals);
      return solverDP->getStatus();
    } break;
    case Options::LinearArithmeticDP::SIMPLEX: {
      solverDP = new DP::SimplexDP(parsedLiterals);
      return solverDP->getStatus();
    } break;
    default: {
      return DecisionProcedure::UNKNOWN;
    } break;
  }
}

unsigned LinearArithmeticDP::getUnsatCoreCount()
{
  if (parsedLiterals.size() < 1)
    return 0;

  if (solverDP == NULL) {
    return 0;
  }

  return solverDP->getUnsatCoreCount();
}

void LinearArithmeticDP::getUnsatCore(LiteralStack &res, unsigned coreIndex)
{
  if (parsedLiterals.size() < 1 || solverDP == NULL) {
    return;
  }

  set<unsigned> unsatCore = solverDP->getUnsatCore(coreIndex);
  if (unsatCore.size() > 0) {
    for (auto &rowIndex : unsatCore) {
      res.push(parsedLiterals[rowIndex].parent);
    }
  }
}

void LinearArithmeticDP::getModel(LiteralStack &model)
{
  CALL("LinearArithmeticDP::getModel");
#if DLADP
  cout << "LinearArithmeticDP::getModel" << endl;
#endif
  if (solverDP != NULL) {
    map<unsigned, RationalConstantType> modelMap = solverDP->getModel();

    for (auto const &result : modelMap) {
      unsigned varId = result.first;
      RationalConstantType solution = result.second;
      unsigned sort = env.signature->getFunction(varId)->fnType()->result();
      switch (sort) {
        case Sorts::SRT_INTEGER: {
          if (!solution.isInt())
            continue;

          Term *var = Term::createConstant(varId);
          Term *constant = theory->representConstant(IntegerConstantType(solution.numerator()));
          Literal *lit = Literal::createEquality(true, TermList(var), TermList(constant), sort);
#if DLADP
          cout << lit->toString() << endl;
#endif
          model.push(lit);
        } break;
        case Sorts::SRT_RATIONAL: {
          Term *var = Term::createConstant(varId);
          Term *constant = theory->representConstant(solution);
          Literal *lit = Literal::createEquality(true, TermList(var), TermList(constant), sort);
#if DLADP
          cout << lit->toString() << endl;
#endif
          model.push(lit);
        } break;
        case Sorts::SRT_REAL: {
          Term *var = Term::createConstant(varId);
          Term *constant = theory->representConstant(RealConstantType(solution));
          Literal *lit = Literal::createEquality(true, TermList(var), TermList(constant), sort);
#if DLADP
          cout << lit->toString() << endl;
#endif
          model.push(lit);
        } break;
        default:
          continue;
          break;
      }
    }
  }
}

#if UseCache
bool LinearArithmeticDP::addSolverDPIfInCache()
{
  if (cache.solverType != env.options->ladp()) {
    return false;
  }

  if (parsedLiterals.size() != cache.constraints.size()) {
    return false;
  }

  // check that parsedLiterals == cache.constraints
  for (unsigned i = 0; i < parsedLiterals.size(); i++) {
    if (parsedLiterals[i].parent != cache.constraints[i]) {
      return false;
    }
  }

#if DLADP
  cout << "SolverDP in cache" << endl;
#endif

  // In cache
  // set up solverDP
  solverDP = cache.solverDP;

  return true;
}

bool LinearArithmeticDP::addConstraintIfInCache(Literal *lit)
{
  if (cache.solverType != env.options->ladp()) {
    return false;
  }

  // Check in cache
  if (cache.parsedLiterals.find(lit) == cache.parsedLiterals.end()) {
    return false;
  }

#if DLADP
  cout << lit->toString() << ", found in cache." << endl;
#endif

  Interpretation predicate = theory->interpretPredicate(lit->functor());
  if (predicate == Interpretation::EQUAL && env.options->ladp() == Options::LinearArithmeticDP::SIMPLEX) {
    // make them two
    // Less Equal
    Constraint parDataLessEqual;
    // multiple by -1
    for (auto const &parameter : cache.parsedLiterals[lit].parameters) {
      parDataLessEqual.parameters[parameter.first] = -parameter.second;
    }
    parDataLessEqual.constant = -cache.parsedLiterals[lit].constant;
    parDataLessEqual.predicate = Interpretation::RAT_LESS_EQUAL;
    parDataLessEqual.parent = lit;
    parsedLiterals.push_back(parDataLessEqual);

    // Greater Equal
    parsedLiterals.push_back(cache.parsedLiterals[lit]);
  }
  else {
    parsedLiterals.push_back(cache.parsedLiterals[lit]);
  }

  return true;
}
#endif

} // namespace DP
