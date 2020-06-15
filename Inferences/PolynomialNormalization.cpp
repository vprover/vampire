#include "Inferences/PolynomialNormalization.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Ordering.hpp"

#define DEBUG(...) // DBG(__VA_ARGS__)

namespace Inferences {

Clause* PolynomialNormalization::simplify(Clause* cl_) {
  auto& cl = *cl_;
  Stack<Literal*> out(cl.size());

  bool changed = false;

  for (int i = 0; i < cl.size(); i++) {

    auto orig = cl[i];
    try {
      auto simpl = _normalizer.evaluate(orig);

      if (simpl.isConstant()) {
        bool trivialValue = simpl.unwrapConstant();
        if (trivialValue) {
          return NULL;
        } else {
          /* do not add the literal to the output stack */
        }
      } else {
        Literal* simplLit = simpl.unwrapLiteral();


        auto cmp = _ordering.compare(simplLit, orig);
        if (cmp == Ordering::Result::LESS) {

          if (simplLit != orig) {
            changed = true;
          }
          out.push(simplLit);

        } else {
          out.push(orig);
        }


        // if (env.options->literalComparisonMode() == Options::LiteralComparisonMode::REVERSE && cl[i]->isNegative())  {
        //   //TODO this is so ugly. We should make a constraint between these options
        //   cmp = Ordering::reverse(cmp);
        // }
        // switch(cmp) {
        //
        // case Ordering::Result::LESS:
        //   //TODO shall we add an assertion here?
        //   out.push(simplLit);
        //   changed = true;
        //   break;
        // case Ordering::Result::INCOMPARABLE:
        // case Ordering::Result::EQUAL:
        //   out.push(cl[i]);
        //   break;
        // case Ordering::GREATER:
        //   DBG("orig:  ", *cl[i])
        //   DBG("simpl: ", *simplLit)
        //   { ASSERTION_VIOLATION }
        // default:
        //   { ASSERTION_VIOLATION }
        // }
      }
    } catch (MachineArithmeticException) {
      out.push(orig);
    }
  }


  if (!changed) {
    return cl_;
  } else {
    auto result = Clause::fromStack(out, SimplifyingInference1(InferenceRule::EVALUATION, cl_));
    DEBUG("in:  ", *cl_)
    DEBUG("out: ", *result)
    return result;
  }
}

PolynomialNormalization::~PolynomialNormalization() {}
} // Inferences
