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
 * Corresponds to the branches of a function definition.
 * Stores the branches and the active positions
 * (i.e. the changing arguments) of the function.
 */
struct InductionTemplate {
  bool checkUsefulness();
  bool checkWellFoundedness();
  bool checkWellDefinedness(vvector<vvector<TermList>>& missingCases);
  void addMissingCases(const vvector<vvector<TermList>>& missingCases);

  /**
   * Stores the template for a recursive case
   * This includes:
   * - the step case
   * - the recursive calls
   *   (if not present it is a base case)
   */
  struct Branch {
    Branch(const vvector<TermList>& recursiveCalls, TermList header)
      : _recursiveCalls(recursiveCalls), _header(header) {}

    Branch(TermList base)
      : _recursiveCalls(), _header(base) {}

    bool contains(Branch other);

    vvector<TermList> _recursiveCalls;
    TermList _header;
  };

  void addBranch(vvector<TermList>&& recursiveCalls, TermList&& header);

  vvector<Branch> _branches;
  vvector<bool> _inductionPositions;
};

ostream& operator<<(ostream& out, const InductionTemplate::Branch& branch);
ostream& operator<<(ostream& out, const InductionTemplate& templ);

/**
 * This class generates the induction templates based on
 * the marked recursive function definitions from the parser.
 */
struct InductionPreprocessor {
  static void preprocessProblem(Problem& prb);
  static bool checkWellFoundedness(const vvector<pair<TermList,TermList>>& relatedTerms);
};

} // Shell

#endif
