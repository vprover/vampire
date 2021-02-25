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
 * @file InductionPreprocessor.hpp
 * Defines helper classes for induction templates and preprocessing
 */

#ifndef __InductionPreprocessor__
#define __InductionPreprocessor__

#include "Forwards.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermTransformer.hpp"
#include "Lib/STL.hpp"

namespace Shell {

using namespace Kernel;
using namespace Lib;

bool isTermAlgebraCons(TermList t);

/**
 * TermTransformer subclass for any TermList to TermList replacement
 */
class TermListReplacement : public TermTransformer {
public:
  TermListReplacement(TermList o, TermList r) : _o(o), _r(r) {}
  TermList transformSubterm(TermList trm) override;
private:
  TermList _o; // to be replaced
  TermList _r; // replacement
};

/**
 * Stores the template for a recursive case
 * This includes:
 * - the step case
 * - the recursive calls
 *   (if not present it is a base case)
 */
struct RDescription {
  RDescription(const vvector<TermList>& recursiveCalls,
               TermList step,
               const vvector<Formula*>& conditions)
    : _recursiveCalls(recursiveCalls), _step(step), _conditions(conditions) {}

  RDescription(TermList step, const vvector<Formula*>& conditions)
    : _recursiveCalls(), _step(step), _conditions(conditions) {}

  vvector<TermList> _recursiveCalls;
  TermList _step;
  vvector<Formula*> _conditions;
};

ostream& operator<<(ostream& out, const RDescription& rdesc);

/**
 * Corresponds to a recursive function definition.
 * Stores the RDescriptions and the active positions
 * (i.e. the induction variables) of the function.
 */
struct InductionTemplate {
  bool checkUsefulness();
  bool checkWellFoundedness();
  bool checkWellDefinedness(vvector<vvector<TermList>>& missingCases);
  void addMissingCases(const vvector<vvector<TermList>>& missingCases);

  enum class VarType {
    SUBTERM,
    FIXED,
    OTHER,
  };
  using VarOrder = vvector<vset<unsigned>>;

  vvector<RDescription> _rDescriptions;
  vvector<bool> _inductionVariables;
  VarOrder _order;

private:
  bool findVarOrder(
    const vvector<vvector<VarType>>& relations,
    vset<unsigned>& candidates,
    VarOrder& res);
};

ostream& operator<<(ostream& out, const InductionTemplate& templ);

/**
 * This class generates the induction templates based on
 * the marked recursive function definitions from the parser.
 */
struct InductionPreprocessor {
static void preprocessProblem(Problem& prb);
static void processFormulaBody(Formula* body, Literal* header, vvector<Formula*> conditions, InductionTemplate& templ);
static void processBody(TermList body, TermList header, vvector<Formula*> conditions, InductionTemplate& templ);
};

} // Shell

#endif
