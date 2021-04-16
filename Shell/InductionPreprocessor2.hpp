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

#ifndef __InductionPreprocessor2__
#define __InductionPreprocessor2__

#include "Forwards.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermTransformer.hpp"
#include "Lib/STL.hpp"
#include "InductionPreprocessor.hpp"

namespace Shell {

using namespace Kernel;
using namespace Lib;

/**
 * This class generates the induction templates based on
 * the marked recursive function definitions from the parser.
 */
struct InductionPreprocessor2 {
  static void preprocessProblem(Problem& prb);
};

} // Shell

#endif
