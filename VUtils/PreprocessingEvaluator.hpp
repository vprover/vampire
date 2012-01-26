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
