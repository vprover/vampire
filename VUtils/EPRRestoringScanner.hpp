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
    FORM_NON_EPR = 3,
    UNDEF
  };

  Options _opts;

  unsigned _predDefCnt;

  unsigned _baseClauseCnt;
  unsigned _erClauseCnt;

  unsigned _baseNonEPRClauseCnt;
  unsigned _erNonEPRClauseCnt;

  EprResult _eprRes;

  void countClauses(Problem& prb, unsigned& allClauseCnt, unsigned& nonEprClauseCnt);

  void computeEprResults();
  void reportResult(EprResult res);
};

}

#endif // __EPRRestoringScanner__
