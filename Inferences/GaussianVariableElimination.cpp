#include "GaussianVariableElimination.hpp"
#include "Kernel/Rebalancing.hpp"
#include "Kernel/Rebalancing/Inverters.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/InterpretedLiteralEvaluator.hpp"
#include "Inferences/InterpretedEvaluation.hpp"
#include "Kernel/PolynomialNormalizer.hpp"

#define DEBUG(...)  //DBG(__VA_ARGS__)

namespace Inferences {
  using Balancer = Kernel::Rebalancing::Balancer<Kernel::Rebalancing::Inverters::NumberTheoryInverter>;

Clause* GaussianVariableElimination::simplify(Clause* in) 
{
  auto ev = PolynomialNormalizer<PolynomialNormalizerConfig::Simplification<>>();
  CALL("GaussianVariableElimination::simplify")
  ASS(in)

  auto& cl = *in;
  
  for(int i = 0; i < cl.size(); i++) {
    auto& lit = *cl[i];
    if (lit.isEquality() && lit.isNegative()) { 
      for (auto b : Balancer(lit)) {

        /* found a rebalancing: lhs = rhs[lhs, ...] */
        auto lhs = b.lhs();
        auto rhs = b.buildRhs();
        ASS_REP(lhs.isVar(), lhs);

        // TODO check whether evaluation here makes sense
        // rhs = ev.evaluate(rhs);
        if (!rhs.containsSubterm(lhs)) {
          /* lhs = rhs[...] */
          DEBUG(lhs, " -> ", rhs);

          return rewrite(cl, lhs, rhs, i);
        }
      }
    }
  }

  return in;
}

Clause* GaussianVariableElimination::rewrite(Clause& cl, TermList find, TermList replace, unsigned skipLiteral) const 
{
  CALL("GaussianVariableElimination::rewrite");
  // Inference& inf = *new Inference1(Kernel::InferenceRule::GAUSSIAN_VARIABLE_ELIMINIATION, &cl);
  Inference inf(SimplifyingInference1(Kernel::InferenceRule::GAUSSIAN_VARIABLE_ELIMINIATION, &cl));

  auto sz = cl.size() - 1;
  Clause& out = *new(sz) Clause(sz, inf); 
  for (int i = 0; i < skipLiteral; i++) {
    out[i] = EqHelper::replace(cl[i], find, replace);
  }

  for (int i = skipLiteral; i < sz; i++)  {
    out[i] = EqHelper::replace(cl[i+1], find, replace);
  }

  return &out;
}

} // namespace Inferences 
