#include "Inferences/PolynomialNormalization.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Ordering.hpp"

namespace Inferences {

Clause* PolynomialNormalization::simplify(Clause* cl_) {
  auto& cl = *cl_;
  Stack<Literal*> out(cl.size());

  bool changed = false;

  for (int i = 0; i < cl.size(); i++) {

    try {
      auto simpl = _normalizer.evaluate(cl[i]);

      if (simpl.isConstant()) {
        bool trivialValue = simpl.unwrapConstant();
        if (trivialValue) {
          return NULL;
        } else {
          /* do not add the literal to the output stack */
        }
      } else {
        Literal* simplLit = simpl.unwrapLiteral();
        if (_ordering.compare(simplLit, cl[i]) == Ordering::Result::LESS) {
          //TODO shall we add an assertion here?
          out.push(simplLit);
          changed = true;
        } else {
          DBG(*cl[i])
          DBG(*simplLit)
          ASS_EQ(cl[i], simplLit)
          out.push(cl[i]);
        }
      }
    } catch (MachineArithmeticException) {
      out.push(cl[i]);
    }
  }


  if (!changed) {
    return cl_;
  } else {

    auto result = Clause::fromStack(out, SimplifyingInference1(InferenceRule::EVALUATION, cl_));
    DBG("finished ", *result)
    return result;
  }
}

PolynomialNormalization::~PolynomialNormalization() {}
} // Inferences
