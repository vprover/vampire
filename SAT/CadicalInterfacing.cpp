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
 * @file CadicalInterfacing.cpp
 * Implements class CadicalInterfacing
 */

#include "cadical/src/tracer.hpp"

#include "CadicalInterfacing.hpp"
#include "SATInference.hpp"

#include "Lib/Array.hpp"

namespace SAT
{

using namespace Shell;
using namespace Lib;

CadicalInterfacing::CadicalInterfacing()
{
  // these help a bit both for avataring and FMB
  _solver.set("phase",0);
  _solver.set("stabilizeonly",1);

  // shush
  _solver.set("quiet",1);
}

Status CadicalInterfacing::solveUnderAssumptionsLimited(const SATLiteralStack& assumps, unsigned conflictCountLimit)
{
  // load assumptions:
  SATLiteralStack::ConstIterator it(assumps);
  _assumptions.clear();
  while (it.hasNext()) {
    _assumptions.push_back(vampire2Cadical(it.next()));
  }

  solveModuloAssumptionsAndSetStatus(conflictCountLimit);
  return _status;
}

SATLiteralStack CadicalInterfacing::failedAssumptions() {
  ASS_EQ(_status, Status::UNSATISFIABLE)

  SATLiteralStack result;
  for(int v : _assumptions)
    if(_solver.failed(v))
      result.push(cadical2Vampire(v).opposite());
  return result;
}

struct Tracer : public CaDiCaL::Tracer {
  // map CaDiCaL clause IDs to Vampire SAT clauses
  ZIArray<SATClause *> cadical2vampire;

  // the current input clause that is being added to the solver
  // this allows us to associate Vampire clauses with CaDiCaL clauses
  SATClause *currentInput = nullptr;
  SATClause *empty = nullptr;

  void add_original_clause(
    uint64_t id,
    bool redundant,
    const std::vector<int> &clause,
    bool restored
  ) override {
    ASS(currentInput)
    cadical2vampire[id] = currentInput;
    currentInput = nullptr;
  }

  void add_derived_clause(
    uint64_t id,
    bool redundant,
    const std::vector<int> &lits,
    const std::vector<uint64_t> &antecedents
  ) override {
    auto cl = new(lits.size()) SATClause(lits.size());
    cadical2vampire[id] = cl;
    for(size_t i = 0; i < lits.size(); i++)
      (*cl)[i] = lits[i];
    SATClauseList *premises = nullptr;
    for(uint64_t antecedent : antecedents)
      SATClauseList::push(cadical2vampire[antecedent], premises);
    // PropInference takes ownership of `premises`
    cl->setInference(new PropInference(premises));
    if(lits.empty())
      empty = cl;
  }
};

SATClause *CadicalInterfacing::proof(SATClauseList* premises) {
  CadicalInterfacing solver;

  auto tracer = new Tracer;
  solver._solver.connect_proof_tracer(tracer, true);
  // ownership of tracer transferred to CaDiCaL: no leak here, at least for now

  for(SATClause *cl : iterTraits(premises->iter())) {
    tracer->currentInput = cl;
    solver.addClause(cl);
  }
  ALWAYS(solver.solve() == Status::UNSATISFIABLE)
  ASS(tracer->empty)
  return tracer->empty;
}

/**
 * Solve modulo assumptions and set status.
 * @b conflictCountLimit as with addAssumption.
 */
void CadicalInterfacing::solveModuloAssumptionsAndSetStatus(unsigned conflictCountLimit)
{
  _solver.limit("conflicts", conflictCountLimit);
  for(int assumption : _assumptions)
    _solver.assume(assumption);
  int res = _solver.solve();

  if (res == CaDiCaL::SATISFIABLE) {
    _status = Status::SATISFIABLE;
  } else if (res == CaDiCaL::UNSATISFIABLE) {
    _status = Status::UNSATISFIABLE;
  } else {
    _status = Status::UNKNOWN;
  }
}

/**
 * Add clause into the solver.
 *
 */
void CadicalInterfacing::addClause(SATClause* cl)
{
  // TODO: consider measuring time
  ASS_EQ(_assumptions.size(),0);

  unsigned clen=cl->length();
  for(unsigned i=0;i<clen;i++) {
    SATLiteral l = (*cl)[i];
    _solver.add(vampire2Cadical(l));
  }
  _solver.add(0);
}

VarAssignment CadicalInterfacing::getAssignment(unsigned var)
{
  ASS_EQ(_status, Status::SATISFIABLE);
  ASS_G(var,0); ASS_L((int)var,_next);

  if((int)var > _solver.vars())
    return VarAssignment::DONT_CARE;
  int phase = _solver.val(var);
  return phase > 0 ? VarAssignment::TRUE : VarAssignment::FALSE;
}

bool CadicalInterfacing::isZeroImplied(unsigned var)
{
  ASS_G(var,0); ASS_L((int)var, _next);
  return _solver.fixed(var);
}

} // namespace SAT
