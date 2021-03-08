/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#include "GaussianVariableElimination.hpp"
#include "Kernel/Rebalancing.hpp"
#include "Kernel/Rebalancing/Inverters.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/InterpretedLiteralEvaluator.hpp"
#include "Inferences/InterpretedEvaluation.hpp"
#include "Kernel/PolynomialNormalizer.hpp"
#include "Shell/Statistics.hpp"

#define DEBUG(...)  //DBG(__VA_ARGS__)

namespace Inferences {

using Balancer = Kernel::Rebalancing::Balancer<Kernel::Rebalancing::Inverters::NumberTheoryInverter>;

SimplifyingGeneratingInference1::Result GaussianVariableElimination::simplify(Clause* in, bool doCheckOrdering) 
{
  CALL("GaussianVariableElimination::simplify")
  ASS(in)

  auto& cl = *in;
  
  for(unsigned i = 0; i < cl.size(); i++) {
    auto& lit = *cl[i];
    if (lit.isEquality() && lit.isNegative()) { 
      for (auto b : Balancer(lit)) {

        /* found a rebalancing: lhs = rhs[lhs, ...] */
        auto lhs = b.lhs();
        auto rhs = b.buildRhs();
        ASS_REP(lhs.isVar(), lhs);

        if (!rhs.containsSubterm(lhs)) {
          /* lhs = rhs[...] */
          DEBUG(lhs, " -> ", rhs);

          return rewrite(cl, lhs, rhs, i, doCheckOrdering);
        }
      }
    }
  }

  return SimplifyingGeneratingInference1::Result{in, false};
}

SimplifyingGeneratingInference1::Result GaussianVariableElimination::rewrite(Clause& cl, TermList find, TermList replace, unsigned skipLiteral, bool doCheckOrdering) const 
{
  CALL("GaussianVariableElimination::rewrite");
  env.statistics->gveCnt++;

  Inference inf(SimplifyingInference1(Kernel::InferenceRule::GAUSSIAN_VARIABLE_ELIMINIATION, &cl));

  bool premiseRedundant = true;

  auto checkLeq = [&](Literal* orig, Literal* rewritten) 
  { 
    if (doCheckOrdering) {
      if (rewritten != orig) {
        // as soon as we rewrite some clause x /= t \/ C[x] into C[t], the result will be incomparable
        // since the weight of t will be at least as big as the weight of x, hence we C[t] won't be smaller 
        // than C[x]
        premiseRedundant = false;
      }
    }
    return rewritten;
  };

  auto sz = cl.size() - 1;
  Clause& out = *new(sz) Clause(sz, inf); 
  for (unsigned i = 0; i < skipLiteral; i++) {
    out[i] = checkLeq(cl[i], EqHelper::replace(cl[i], find, replace));
  }

  for (unsigned i = skipLiteral; i < sz; i++)  {
    out[i] = checkLeq(cl[i+1], EqHelper::replace(cl[i+1], find, replace));
  }

  if(!premiseRedundant) {
    env.statistics->gveViolations++;
  }

  return SimplifyingGeneratingInference1::Result{&out, premiseRedundant};
}

} // namespace Inferences 
