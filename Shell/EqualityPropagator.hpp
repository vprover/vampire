/**
 * @file EqualityPropagator.hpp
 * Defines class EqualityPropagator.
 */

#ifndef __EqualityPropagator__
#define __EqualityPropagator__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/Term.hpp"

namespace Shell {

using namespace Lib;
using namespace Kernel;

/**
 * Propagate equalities in formulas, for example
 * X=Y => X=f(Y) ---> X=f(X)
 *
 * The input formulas must be rectified, flattened, without
 * TRUE and FALSE subformulas and without free variables,
 * these properties are preserved.
 */
class EqualityPropagator {
public:
  EqualityPropagator(bool trace=false) : _trace(trace) {}

  void apply(UnitList*& units);
  Unit* apply(Unit* u);
  TermList apply(unsigned var);
private:

  class SingletonVariableRemover;

  FormulaUnit* apply(FormulaUnit* u);
  Formula* apply(Formula* form);
  Formula* applyTopLevel(Formula* form);

  Formula* apply(JunctionFormula* form);
  Formula* apply(QuantifiedFormula* form);
  Literal* apply(Literal* l);

  int getVarPolarity(unsigned var);

  void collectResolvableBindings(Formula* form, bool negated);

  void undoBindings(unsigned remaining);

  bool _trace;

  Stack<unsigned> _vars;
  DHMap<unsigned,unsigned> _varDepths;

  Stack<unsigned> _boundVars;
  DHMap<unsigned,TermList> _varBindings;
};

}

#endif // __EqualityPropagator__
