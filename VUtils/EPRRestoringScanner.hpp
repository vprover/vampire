/**
 * @file EPRRestoringScanner.hpp
 * Defines class EPRRestoringScanner.
 */

#ifndef __EPRRestoringScanner__
#define __EPRRestoringScanner__

#include "Forwards.hpp"

#include "Shell/Options.hpp"


namespace VUtils {

using namespace Shell;

class EPRRestoringScanner {
public:
  int perform(int argc, char** argv);
private:
  enum EprResult {
    MADE_EPR_WITH_RESTORING = 0,
    CANNOT_MAKE_EPR = 1,
    EASY_EPR = 2,
    FORM_NON_EPR = 3
  };

  Options _opts;

  void reportResultAndExit(EprResult res) NO_RETURN;
};

}

#endif // __EPRRestoringScanner__
