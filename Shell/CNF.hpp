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
 * @file CNF.hpp
 * Defines class CNF implementing CNF transformation.
 * @since 19/01/2004 Manchester
 * @since 27/12/2007 Manchester, changed completely to a new implementation
 */

#ifndef __CNF__
#define __CNF__

#include "Lib/Stack.hpp"
#include "Lib/ProofExtra.hpp"
#include <utility>
#include <vector>

namespace Kernel {
  class Formula;
  class FormulaUnit;
  class Clause;
  class Unit;
  class Literal;
};

using namespace Lib;
using namespace Kernel;

namespace Shell {

/** Captured by CNF before selection changes literal order. Occurrences
 * follow the printed parent and retain its equality orientations. */
struct ClausificationExtra : Lib::InferenceExtra {
  struct Occurrence {
    Kernel::Literal* instantiated;
    bool flipped;
  };
  std::vector<std::pair<unsigned, unsigned>> binders;
  std::vector<Occurrence> occurrences;
  void output(std::ostream& out) const override { out << "clausification_certificate"; }
};

/**
 * Class implementing the CNF transformation.
 * @since 19/01/2004 Manchester
 */
class CNF
{
public:
  CNF();
  void clausify (Unit*,Stack<Clause*>& stack);
private:
  void clausify(Formula*);
  void recordClausification(Clause* conclusion);
  // the original recurisive version (for documentation and reference)
  // void clausify_rec(Formula*);
  /** The unit currently being processed */
  FormulaUnit* _unit;
  /** stack to collect the results */
  Stack<Clause*>* _result;
  /** stack of literals collected so far */
  Stack <Literal*> _literals;
  /** stack of formulas  */
  Stack <Formula*> _formulas;
}; // class CNF

}
#endif
