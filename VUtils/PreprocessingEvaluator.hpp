
/*
 * File PreprocessingEvaluator.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file PreprocessingEvaluator.hpp
 * Defines class PreprocessingEvaluator.
 */

#ifndef __PreprocessingEvaluator__
#define __PreprocessingEvaluator__

#include "Forwards.hpp"

#include "Lib/Timer.hpp"



namespace VUtils {

using namespace Lib;
using namespace Kernel;
using namespace Shell;

class PreprocessingEvaluator {
public:
  int perform(int argc, char** argv);

private:
  void printStatistics(Problem& prb);

  Timer _parsing;
  Timer _preproc;
};

}

#endif // __PreprocessingEvaluator__
