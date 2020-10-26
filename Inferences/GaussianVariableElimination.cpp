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

  bool allLessEq = true;

  auto checkLeq = [&](Literal* orig, Literal* rewritten) 
  { 
    if (doCheckOrdering) {
      auto ord = Ordering::tryGetGlobalOrdering();
      ASS(ord)
      auto cmp = ord->compare(rewritten, orig);
      switch(cmp) {
        case Ordering::Result::LESS:
        case Ordering::Result::LESS_EQ:
        case Ordering::Result::EQUAL:
          break;
        case Ordering::Result::INCOMPARABLE:
        case Ordering::Result::GREATER:
        case Ordering::Result::GREATER_EQ:
          allLessEq = false;
          break;
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

  auto premiseRedundant = allLessEq;
  if(!premiseRedundant) {
    env.statistics->gveViolations++;
  }
  return SimplifyingGeneratingInference1::Result{&out, premiseRedundant};
}

} // namespace Inferences 
