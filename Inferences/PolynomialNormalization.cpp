#include "Inferences/PolynomialNormalization.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Ordering.hpp"
#include "Shell/Statistics.hpp"

#define DEBUG(...) //DBG(__VA_ARGS__)

namespace Inferences {

Clause* PolynomialNormalization::simplify(Clause* cl_) {
  CALL("PolynomialNormalization::simplify(Clause*)")
  DEBUG("in:  ", *cl_)
  auto& cl = *cl_;
  Stack<Literal*> out(cl.size());

  bool changed = false;

  for (int i = 0; i < cl.size(); i++) {

    auto orig = cl[i];
    try {
      auto simpl = _normalizer.evaluate(orig);

      if (simpl.isConstant()) {
        env.statistics->polyNormalizerSimplAttempts++;
        env.statistics->polyNormalizerSimplSuccess++;

        bool trivialValue = simpl.unwrapConstant();
        if (trivialValue) {
          /* clause is a tautology and can be deleted */
          return NULL;
        } else {
          /* do not add the literal to the output stack */
          changed = true;
        }
      } else {
        Literal* simplLit = simpl.unwrapLiteral();
        if (simplLit != orig)
          env.statistics->polyNormalizerSimplAttempts++;

        if (_ordering != nullptr &&
            _ordering->compare(simplLit, orig) == Ordering::Result::LESS) {

          ASS(simplLit != orig)
          env.statistics->polyNormalizerSimplSuccess++;
          changed = true;
          out.push(simplLit);

        } else {
          out.push(orig);
        }
      }
    } catch (MachineArithmeticException) {
      out.push(orig);
    }
  }


  if (!changed) {
    return cl_;
  } else {
    auto result = Clause::fromStack(out, SimplifyingInference1(InferenceRule::EVALUATION, cl_));
    DEBUG("out: ", *result)
    return result;
  }
}

PolynomialNormalization::~PolynomialNormalization() {}
} // Inferences
