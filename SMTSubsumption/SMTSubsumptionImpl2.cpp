#include "SMTSubsumptionImpl2.hpp"
#include "Util.hpp"
#include "Kernel/Matcher.hpp"
#include "Debug/RuntimeStatistics.hpp"
#include <iostream>

using namespace Indexing;
using namespace Kernel;
using namespace SMTSubsumption;

// TODO: early exit in case time limit hits, like in MLMatcher which checks every 50k iterations if time limit has been exceeded

// The ground literal prefilter seems to slow us down slightly in general.
// Maybe it's more helpful with induction enabled? since that adds a lot of ground clauses.
#define GROUND_LITERAL_PREFILTER 0








SMTSubsumptionImpl2::SMTSubsumptionImpl2()
{
  solver.reserve_variables(64);
  solver.reserve_clause_storage(512);
  solver.theory().reserve(64, 2, 16);
  bm.reserve(64, 2, 16);
  instance_constraints.reserve(16);
}



/// Set up the subsumption problem.
/// Returns false if no solution is possible.
/// Otherwise, solve() needs to be called.
bool SMTSubsumptionImpl2::setupSubsumption(Kernel::Clause* base, Kernel::Clause* instance)
{
  CALL("SMTSubsumptionImpl2::setupSubsumption");
  solver.clear();
  ASS(solver.empty());
  ASS(solver.theory().empty());
  bm.clear();
  ASS(bm.empty());
  solver.theory().setBindings(&bm);

  m_base = base;
  m_instance = instance;

#if GROUND_LITERAL_PREFILTER
  base_used.clear();
  ASS(base_used.empty());
  inst_used.clear();
  ASS(inst_used.empty());

  inst_used.resize(instance->length(), false);

  uint32_t base_ground = 0;
  for (unsigned i = 0; i < base->length(); ++i) {
    Literal* base_lit = base->literals()[i];
    if (base_lit->ground()) {
      // Find matching ground literal
      for (unsigned j = 0; j < instance->length(); ++j) {
        Literal* inst_lit = instance->literals()[j];
        if (!inst_used[j] && base_lit == inst_lit) {
          base_used.push_back(true);
          inst_used[j] = true;
          break;
        }
      }
      // No matching ground literal => cannot be subsumed
      if (!base_used[i]) {
        return false;
      }
      base_ground += 1;
    } else {
      base_used.push_back(false);
    }
  }

  uint32_t const remaining_base_len = base->length() - base_ground;
#else
  uint32_t const remaining_base_len = base->length();
#endif

/*
  uint32_t base_n_commutative = 0;
  for (unsigned i = 0; i < base->length(); ++i) {
    Literal* base_lit = base->literals()[i];
    if (base_lit->commutative()) {
      base_n_commutative += 1;
    }
  }
*/

  // Here we store the AtMostOne constraints saying that each instance literal may be matched at most once.
  // Each instance literal can be matched by at most 2 boolean vars per base literal (two orientations of equalities).
  // NOTE: instance constraints cannot be packed densely because we only know their shape at the end.
  uint32_t const instance_constraint_maxsize = 2 * remaining_base_len;
  instance_constraints.clear();
  ASS(instance_constraints.empty());
  for (size_t i = 0; i < instance->length(); ++i) {
    instance_constraints.push_back(solver.alloc_constraint(instance_constraint_maxsize));
  }

  // Matching for subsumption checks whether
  //
  //      side_premise\theta \subseteq main_premise
  //
  // holds.
  for (unsigned i = 0; i < base->length(); ++i) {
    Literal* base_lit = base->literals()[i];
    uint32_t match_count = 0;

#if GROUND_LITERAL_PREFILTER
    if (base_used[i]) {
      continue;
    }
#endif

    // Build clause stating that base_lit must be matched to at least one corresponding instance literal.
    // NOTE: we do not need an AtMostOne constraint with the same literals, because
    //       1) different literals will induce different substitutions so this is already built-in via the theory propagation (and because we don't have clauses with duplicate literals)
    //       2) even if 1) were false, a solution with multiple matches could always be reduced to a solution with one match per literal.
    solver.constraint_start();

    for (unsigned j = 0; j < instance->length(); ++j) {
      Literal* inst_lit = instance->literals()[j];

#if GROUND_LITERAL_PREFILTER
      if (inst_used[j]) {
        continue;
      }
#endif
      if (!Literal::headersMatch(base_lit, inst_lit, false)) {
        continue;
      }

      {
        auto binder = bm.start_binder();
        if (base_lit->arity() == 0 || MatchingUtils::matchArgs(base_lit, inst_lit, binder)) {
          subsat::Var b = solver.new_variable(i);
          // std::cerr << "Match: " << b << " => " << base_lit->toString() << " -> " << inst_lit->toString() << std::endl;

#if GROUND_LITERAL_PREFILTER
          ASS(!base_lit->ground());
#endif
          if (binder.size() > 0) {
            ASS(!base_lit->ground());
          } else {
            ASS(base_lit->ground());
            ASS_EQ(base_lit, inst_lit);
            // TODO: in this case, at least for subsumption, we should skip this base_lit and this inst_list.
            // probably best to have a separate loop first that deals with ground literals? since those are only pointer equality checks.
          }

          bm.commit_bindings(binder, b);

          solver.constraint_push_literal(b);
          solver.handle_push_literal(instance_constraints[j], b);
          match_count += 1;
        }
      }

      if (base_lit->commutative()) {
        ASS_EQ(base_lit->arity(), 2);
        ASS_EQ(inst_lit->arity(), 2);
        auto binder = bm.start_binder();
        if (MatchingUtils::matchReversedArgs(base_lit, inst_lit, binder)) {
          subsat::Var b = solver.new_variable(i);

          if (binder.size() > 0) {
            ASS(!base_lit->ground());
          } else {
            ASS(base_lit->ground());
            ASS_EQ(base_lit, inst_lit);
            // TODO: in this case, at least for subsumption, we should skip this base_lit and this inst_list.
            // probably best to have a separate loop first that deals with ground literals? since those are only pointer equality checks.
          }

          bm.commit_bindings(binder, b);

          solver.constraint_push_literal(b);
          solver.handle_push_literal(instance_constraints[j], b);
          match_count += 1;
        }
      }
    }
    auto handle = solver.constraint_end();
    solver.add_clause_unsafe(handle);

    // If there are no matches for this base literal, we have just added an empty clause.
    // => conflict on root level due to empty clause, abort early
    // if (match_count == 0) { ASS(solver.inconsistent()); }
    // if (solver.inconsistent()) {
    //   return false;
    // }
    if (match_count == 0) {
      return false;
    }
  }

  for (auto& handle : instance_constraints) {
    auto built = solver.handle_build(handle);
    solver.add_atmostone_constraint_unsafe(built);
  }

  return !solver.inconsistent();
}  // setupSubsumption



/// Set up the subsumption resolution problem from scratch.
/// Returns false if no solution is possible.
/// Otherwise, solve() needs to be called.
bool SMTSubsumptionImpl2::setupSubsumptionResolution(Kernel::Clause* base, Kernel::Clause* instance)
{
  CALL("SMTSubsumptionImpl2::setupSubsumptionResolution");
  solver.clear();
  ASS(solver.empty());
  ASS(solver.theory().empty());
  bm.clear();
  ASS(bm.empty());
  solver.theory().setBindings(&bm);
  complementary_matches.clear();
  ASS(complementary_matches.empty());

  // TODO: improve allocation behaviour
  inst_normal_matches.clear();
  inst_normal_matches.resize(instance->length());
  inst_compl_matches.clear();
  inst_compl_matches.resize(instance->length());
  inst_is_compl_matched.clear();
  inst_is_compl_matched.reserve(instance->length());

  m_base = base;
  m_instance = instance;

  for (unsigned i = 0; i < base->length(); ++i) {
    Literal* const base_lit = base->literals()[i];
    uint32_t match_count = 0;

    // Build clause stating that base_lit must be matched to at least one corresponding instance literal.
    solver.constraint_start();

    for (unsigned j = 0; j < instance->length(); ++j) {
      Literal* const inst_lit = instance->literals()[j];

      // Same-polarity match (subsumption part)
      if (Literal::headersMatch(base_lit, inst_lit, false)) {
        {
          auto binder = bm.start_binder();
          if (base_lit->arity() == 0 || MatchingUtils::matchArgs(base_lit, inst_lit, binder)) {
            subsat::Var b = solver.new_variable(i);
            bm.commit_bindings(binder, b);
            solver.constraint_push_literal(b);
            inst_normal_matches[j].push_back(b);
            match_count += 1;
          }
        }
        if (base_lit->commutative()) {
          auto binder = bm.start_binder();
          if (MatchingUtils::matchReversedArgs(base_lit, inst_lit, binder)) {
            subsat::Var b = solver.new_variable(i);
            bm.commit_bindings(binder, b);
            solver.constraint_push_literal(b);
            inst_normal_matches[j].push_back(b);
            match_count += 1;
          }
        }
      }

      // Complementary match (subsumption resolution part)
      if (Literal::headersMatch(base_lit, inst_lit, true)) {
        {
          auto binder = bm.start_binder();
          if (base_lit->arity() == 0 || MatchingUtils::matchArgs(base_lit, inst_lit, binder)) {
            subsat::Var b = solver.new_variable(i);
            bm.commit_bindings(binder, b);
            solver.constraint_push_literal(b);
            complementary_matches.push_back({b, j});
            inst_compl_matches[j].push_back(b);
            match_count += 1;
          }
        }
        if (base_lit->commutative()) {
          auto binder = bm.start_binder();
          if (MatchingUtils::matchReversedArgs(base_lit, inst_lit, binder)) {
            subsat::Var b = solver.new_variable(i);
            bm.commit_bindings(binder, b);
            solver.constraint_push_literal(b);
            complementary_matches.push_back({b, j});
            inst_compl_matches[j].push_back(b);
            match_count += 1;
          }
        }
      }
    }

    auto handle = solver.constraint_end();
    solver.add_clause_unsafe(handle);

    // If there are no matches for this base literal, we have just added an empty clause.
    // => conflict on root level due to empty clause, abort early
    if (match_count == 0) {
      return false;
    }
  }

  // At least one complementary match
  // NOTE: this clause is required. Without it, we may get a false subsumption
  //       (because subsumption resolution uses set-matching and not multiset-matching)
  if (complementary_matches.empty()) {
    return false;
  }
  else {
    solver.constraint_start();
    for (auto const pair : complementary_matches) {
      subsat::Var const b = pair.first;
      solver.constraint_push_literal(b);
    }
    auto handle = solver.constraint_end();
    solver.add_clause_unsafe(handle);
  }

  // NOTE: these constraints are necessary because:
  // 1) when an inst_lit is complementary-matched, then we cannot match anything else to it.
  // 2) but when it is not complementary-matched, then we may match multiple base literals to it.
  // The reason 2) is why we can't simply use instance-AtMostOne constraints like we do for subsumption.
  // Naive solution: use binary clauses "~compl \/ ~normal", more sophisticated: use a helper variable that just means "instance literal is complementary-matched".
  //
  // Example of wrong inference without these constraints:
  // % ***WRONG RESULT OF SUBSUMPTION RESOLUTION***
  // %    base:       ~p(X0,X1,X2,X3,X4) | p(X5,X1,X2,X3,X4)
  // %    instance:   ~neq(X10,X11) | ~neq(X10,s0) | ~neq(X12,X11) | ~neq(X10,X12) | ~neq(X10,X13) | ~neq(X12,s0) | ~neq(X13,X14) | ~neq(X13,X11) | ~neq(X10,X14) | p(X10,X13,X14,s0,s0)
  // % Should NOT be possible but found the following result:
  // %    conclusion: ~neq(X10,X11) | ~neq(X10,s0) | ~neq(X12,X11) | ~neq(X10,X12) | ~neq(X10,X13) | ~neq(X12,s0) | ~neq(X13,X14) | ~neq(X13,X11) | ~neq(X10,X14)
  for (unsigned j = 0; j < instance->length(); ++j) {
    uint32_t const nnormal = inst_normal_matches[j].size();
    uint32_t const ncompl = inst_compl_matches[j].size();
    if (nnormal >= 2 && ncompl >= 2 && nnormal + ncompl > 4) {
      // TODO: more sophisticated encoding with helper variable? instead of the 'matrix' encoding below
      RSTAT_CTR_INC("would do SR sophisticated encoding");
    }
    // Idea: instance literal is complementary-matched => cannot be normal-matched
    // basic implementation using binary clauses.
    for (subsat::Var const b_compl : inst_compl_matches[j]) {
      for (subsat::Var const b_normal : inst_normal_matches[j]) {
        solver.constraint_start();
        solver.constraint_push_literal(~b_compl);
        solver.constraint_push_literal(~b_normal);
        auto handle = solver.constraint_end();
        solver.add_clause_unsafe(handle);
      }
    }
  }

  // inst_is_compl_matched[j] is true if instance[j] is complementary-matched by one or more base literals
  // (other direction not required, but we could use it instead of the "at least one complementary match" above)
  for (unsigned j = 0; j < instance->length(); ++j) {
    subsat::Var const b_is_matched = solver.new_variable();
    inst_is_compl_matched.push_back(b_is_matched);
    ASS_EQ(inst_is_compl_matched[j], b_is_matched);
    for (subsat::Var const b_compl : inst_compl_matches[j]) {
      solver.constraint_start();
      solver.constraint_push_literal(~b_compl);
      solver.constraint_push_literal(b_is_matched);
      auto handle = solver.constraint_end();
      solver.add_clause_unsafe(handle);
    }
  }

  // At most one instance literal is complementary-matched.
  // But note that this instance literal may be complementary-matched by multiple base literals!
  solver.constraint_start();
  for (subsat::Var const b_is_matched : inst_is_compl_matched) {
    solver.constraint_push_literal(b_is_matched);
  }
  auto handle2 = solver.constraint_end();
  solver.add_atmostone_constraint_unsafe(handle2);

  return !solver.inconsistent();
  // TODO: second version that transforms the subsumption instance into an SR instance?
  //       Why? because ForwardSubsumptionAndResolution does something similar with caching the ClauseMatches structure.
  //       However, we would have to cache the whole solver. Do we want to do this?
  //       No, actually we could also re-use the matches (store the matches separately and just cache that).
}  // setupSubsumptionResolution


bool SMTSubsumptionImpl2::solve()
{
  CALL("SMTSubsumptionImpl2::solve");
  return solver.solve() == subsat::Result::Sat;
}

Kernel::Clause* SMTSubsumptionImpl2::getSubsumptionResolutionConclusion()
{
  int const conclusion_len = m_instance->length() - 1;
  Clause* conclusion = new (conclusion_len) Clause(conclusion_len,
      SimplifyingInference2(InferenceRule::SUBSUMPTION_RESOLUTION, m_instance, m_base));

  std::uint32_t resolved_idx = UINT32_MAX;
  for (auto const pair : complementary_matches) {
    subsat::Var const b = pair.first;
    if (solver.get_value(b) == subsat::Value::True) {
      resolved_idx = pair.second;
      break;
    }
  }
  ASS_NEQ(resolved_idx, UINT32_MAX);
  Literal* const resolved_lit = m_instance->literals()[resolved_idx];

  unsigned next = 0;
  for (unsigned i = 0; i < m_instance->length(); ++i) {
    Literal* const lit = m_instance->literals()[i];
    if (lit != resolved_lit) {
      (*conclusion)[next++] = lit;
    }
  }
  ASS_EQ(next, conclusion_len);
  return conclusion;
}



bool SMTSubsumptionImpl2::checkSubsumption(Kernel::Clause* base, Kernel::Clause* instance)
{
  CALL("SMTSubsumptionImpl2::checkSubsumption");
  return setupSubsumption(base, instance) && solve();
}



bool SMTSubsumptionImpl2::checkSubsumptionResolution(Kernel::Clause* base, Kernel::Clause* instance, Kernel::Clause* conclusion)
{
  setupSubsumptionResolution(base, instance);
  if (conclusion == nullptr) {
    RSTAT_CTR_INC("failed subsumption resolutions");
    if (solve()) {
      std::cerr << "\% ***WRONG RESULT OF SUBSUMPTION RESOLUTION***" << std::endl;
      std::cerr << "\%    base       = " << base->toString() << std::endl;
      std::cerr << "\%    instance   = " << instance->toString() << std::endl;
      std::cerr << "\% Should NOT be possible but SMT-SR found the following result:" << std::endl;
      std::cerr << "\%    conclusion = " << getSubsumptionResolutionConclusion()->toString() << std::endl;
      return false;
    } else {
      return true;
    }
  }
  int found = 0;
  while (solve()) {
    // Found another model, build the corresponding result
    Kernel::Clause* cl = getSubsumptionResolutionConclusion();
    if (checkClauseEquality(cl, conclusion)) {
      found += 1;
    }
  }
  RSTAT_MCTR_INC("subsumption resolution #possible consequences", found);
  if (found == 0) {
    std::cerr << "\% ***WRONG RESULT OF SUBSUMPTION RESOLUTION***" << std::endl;
    std::cerr << "\%    base     = " << base->toString() << std::endl;
    std::cerr << "\%    instance = " << instance->toString() << std::endl;
    std::cerr << "\% No result from SMT-SR, but should have found this conclusion:" << std::endl;
    std::cerr << "\%    expected = " << conclusion->toString() << std::endl;
  }
  return (found > 0);
}
