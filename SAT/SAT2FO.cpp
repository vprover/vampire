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
 * @file SAT2FO.cpp
 * Implements class SAT2FO.
 */

#include "Kernel/Term.hpp"

#include "SATClause.hpp"
#include "SATInference.hpp"
#include "SATLiteral.hpp"
#include "SATSolver.hpp"

#include "SAT2FO.hpp"

namespace SAT
{

#if VTHREADED_AVATAR
VTHREAD_LOCAL ZIArray<bool> SAT2FO::_our_literals;
#endif

/**
 * Return number of a fresh SAT variable that will not be assigned to any Literal.
 */
unsigned SAT2FO::createSpareSatVar()
{
  CALL("SAT2FO::createSpareSatVar");
#if VTHREADED_AVATAR
    std::lock_guard<std::mutex> lock(_mutex);
#endif
  return _posMap.getSpareNum();
}

SATLiteral SAT2FO::toSAT(Literal* l)
{
  CALL("SAT2FO::toSAT");

  bool pol = l->isPositive();
  Literal* posLit = Literal::positiveLiteral(l);

#if VTHREADED_AVATAR
  std::lock_guard<std::mutex> lock(_mutex);
#endif
  unsigned var = _posMap.get(posLit);
#if VTHREADED_AVATAR
  _our_literals[var] = true;
#endif
  return SATLiteral(var, pol);
}

/**
 * If a FO literal corresponds to the sat literal, return it, otherwise return 0.
 */
Literal* SAT2FO::toFO(SATLiteral sl) const
{
  CALL("SAT2FO::toFO");

#if VTHREADED_AVATAR
  if(!_our_literals[sl.var()]) {
    return nullptr;
  }
  std::lock_guard<std::mutex> lock(_mutex);
#endif
  Literal* posLit;
  if(!_posMap.findObj(sl.var(), posLit)) {
    return 0;
  }
  Literal* res = sl.polarity() ? posLit : Literal::complementaryLiteral(posLit);
  return res;
}

/**
 * Convert clause @c cl to a SAT clause with an inference
 * object describing the conversion.
 * The returned clause does not contain duplicate variables.
 * If the converted clause was a tautology, zero is returned.
 */
SATClause* SAT2FO::toSAT(Clause* cl)
{
  CALL("SAT2FO::toSAT");

  Clause::Iterator cit(*cl);

#if VTHREADED_AVATAR
  VTHREAD_LOCAL static SATLiteralStack satLits;
#else
  static SATLiteralStack satLits;
#endif
  satLits.reset();

  while (cit.hasNext()) {
    Literal* lit = cit.next();
    //check if it is already in the map and/or add it
    SATLiteral slit = toSAT(lit);
    satLits.push(slit);
  }

  SATClause* clause = SATClause::fromStack(satLits);
  clause->setInference(new FOConversionInference(cl));
  clause = SATClause::removeDuplicateLiterals(clause);

  return clause;
}

void SAT2FO::collectAssignment(SATSolver& solver, LiteralStack& res) const
{
  CALL("SAT2FO::collectAssignment");
  // ASS_EQ(solver.getStatus(), SATSolver::SATISFIABLE);
  ASS(res.isEmpty());

  unsigned maxVar = maxSATVar();
#if VTHREADED_AVATAR
  solver.ensureVarCount(maxVar);
#endif
  for (unsigned i = 1; i <= maxVar; i++) {
    SATSolver::VarAssignment asgn = solver.getAssignment(i);
    if(asgn==SATSolver::DONT_CARE) {
      //we don't add DONT_CARE literals into the assignment
      continue;
    }
    ASS(asgn==SATSolver::TRUE || asgn==SATSolver::FALSE);
    SATLiteral sl(i, asgn==SATSolver::TRUE);
#if !VTHREADED_AVATAR
    ASS(solver.trueInAssignment(sl));
#endif
    Literal* lit = toFO(sl);
    if(!lit) {
      //SAT literal doesn't have corresponding FO one
      continue;
    }
    res.push(lit);
  }
}

SATClause* SAT2FO::createConflictClause(LiteralStack& unsatCore, InferenceRule rule)
{
  CALL("SAT2FO::createConflictClause");

#if VTHREADED_AVATAR
  VTHREAD_LOCAL static LiteralStack negStack;
#else
  static LiteralStack negStack;
#endif
  negStack.reset();
  LiteralStack::ConstIterator ucit(unsatCore);
  while(ucit.hasNext()) {
    Literal* ul = ucit.next();
    negStack.push(Literal::complementaryLiteral(ul));
  }
  Clause* foConfl = Clause::fromStack(negStack,NonspecificInference0(UnitInputType::AXIOM,rule));
  return toSAT(foConfl);
}

std::ostream& operator<<(std::ostream& out, SAT2FO const& self)
{ return out << self._posMap; }

} // namespace SAT
