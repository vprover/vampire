#include "SMTSubsumptionImpl3.hpp"
#include "Kernel/Matcher.hpp"
#include "Debug/RuntimeStatistics.hpp"
#include <iostream>

using namespace Indexing;
using namespace Kernel;
using namespace SMTSubsumption;

// TODO: early exit in case time limit hits, like in MLMatcher which checks every 50k iterations if time limit has been exceeded

SMTSubsumptionImpl3::SMTSubsumptionImpl3()
{
  solver.reserve_variables(64);
  solver.reserve_clause_storage(512);
  solver.theory().reserve(64, 2, 16);
  base_clauses.reserve(16);
  instance_constraints.reserve(16);
}



void SMTSubsumptionImpl3::setupMainPremise(Kernel::Clause* new_instance)
{
  instance = new_instance;
  // TODO:
  // Copy the literals into a vvector, std::sort them (like LiteralMiniIndex; by header).
  // Then use std::binary_search to find the first one in setupSubsumption?
}



/// Set up the subsumption problem. Must have called setupMainPremise first.
/// Returns false if no solution is possible.
/// Otherwise, solve() needs to be called.
bool SMTSubsumptionImpl3::setupSubsumption(Kernel::Clause* base)
{
  CALL("SMTSubsumptionImpl3::setupSubsumption");
  solver.clear();
  ASS(solver.empty());
  auto& theory = solver.theory();
  ASS(theory.empty());

  uint32_t const base_len = base->length();
  uint32_t const inst_len = instance->length();

  base_clauses.clear();
  ASS(base_clauses.empty());

  // Here we store the AtMostOne constraints saying that each instance literal may be matched at most once.
  // Each instance literal can be matched by at most 2 boolean vars per base literal (two orientations of equalities).
  // NOTE: instance constraints cannot be packed densely because we only know their shape at the end.
  uint32_t const instance_constraint_maxsize = 2 * base_len;
  instance_constraints.clear();
  ASS(instance_constraints.empty());
  for (size_t i = 0; i < inst_len; ++i) {
    instance_constraints.push_back(solver.alloc_constraint(instance_constraint_maxsize));
  }

  // Pre-matching
  // To keep overhead as low as possible, we do not yet create solver variables at this point
  uint32_t nextVarIndex = 0;
  for (unsigned bi = 0; bi < base_len; ++bi) {
    Literal* base_lit = base->literals()[bi];
    uint32_t match_count = 0;

    for (unsigned j = 0; j < inst_len; ++j) {
      Literal* inst_lit = instance->literals()[j];

      if (!Literal::headersMatch(base_lit, inst_lit, false)) {
        continue;
      }

      {
        auto binder = theory.start_binder();
        if (base_lit->arity() == 0 || MatchingUtils::matchArgs(base_lit, inst_lit, binder)) {
          subsat::Var b{nextVarIndex++};
          // LOG_DEBUG("MatchFwd: " << b << " ~ " << base_lit->toString() << " -> " << inst_lit->toString());
          match_count += 1;
          theory.commit_bindings(binder, b);
          solver.handle_push_literal(instance_constraints[j], b);
        }
      }

      if (base_lit->commutative()) {
        ASS_EQ(base_lit->arity(), 2);
        ASS_EQ(inst_lit->arity(), 2);
        auto binder = theory.start_binder();
        if (MatchingUtils::matchReversedArgs(base_lit, inst_lit, binder)) {
          subsat::Var b{nextVarIndex++};
          // LOG_DEBUG("MatchRev: " << b << " ~ " << base_lit->toString() << " -> " << inst_lit->toString());
          match_count += 1;
          theory.commit_bindings(binder, b);
          solver.handle_push_literal(instance_constraints[j], b);
        }
      }
    }
    base_clauses.push_back(match_count);

    // If there are no matches for this base literal, we will add an empty clause.
    // => conflict on root level due to empty clause, abort early
    if (match_count == 0) {
      return false;
    }
  }

  // Build clauses stating that base_lit must be matched to at least one corresponding instance literal.
  ASS_EQ(base_clauses.size(), base_len);
  for (unsigned bi = 0; bi < base_len; ++bi) {
    uint32_t match_count = base_clauses[bi];
    solver.constraint_start();
    while (match_count--) {
      subsat::Var b = solver.new_variable(bi);
      solver.constraint_push_literal(b);
    }
    auto handle = solver.constraint_end();
    solver.add_clause_unsafe(handle);
  }

  for (auto handle : instance_constraints) {
    auto built = solver.handle_build(handle);
    solver.add_atmostone_constraint_unsafe(built);
  }

  return !solver.inconsistent();
}  // setupSubsumption



bool SMTSubsumptionImpl3::setupSubsumptionResolution(Kernel::Clause* base)
{
  CALL("SMTSubsumptionImpl3::setupSubsumptionResolution");
  solver.clear();
  ASS(solver.empty());
  auto& theory = solver.theory();
  ASS(theory.empty());

  uint32_t const base_len = base->length();
  uint32_t const inst_len = instance->length();

  // TODO
  return false;
}  // setupSubsumptionResolution



bool SMTSubsumptionImpl3::solve()
{
  return solver.solve() == subsat::Result::Sat;
}
