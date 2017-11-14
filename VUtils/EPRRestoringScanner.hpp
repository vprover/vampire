
/*
 * File EPRRestoringScanner.hpp.
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

  bool _useUnitPropagationForSatEqDiscovery;
  bool _useVariableNormalizationForSatEqDiscovery;

  Options _opts;

  void countClauses(Problem& prb, unsigned& allClauseCnt, unsigned& nonEprClauseCnt);
  unsigned countDefinitions(Problem& prb);

  void computeEprResults(Problem& prb);
  unsigned _baseClauseCnt;
  unsigned _baseNonEPRClauseCnt;
  unsigned _erClauseCnt;
  unsigned _erNonEPRClauseCnt;
  EprResult _eprRes;

  void computeInliningResults(Problem& prb);
  unsigned _predDefCnt;
  unsigned _predDefsNonGrowing;
  unsigned _predDefsMerged;
  unsigned _predDefsAfterNGAndMerge;
  unsigned _ngmClauseCnt;
  unsigned _ngmNonEPRClauseCnt;
  unsigned _satDiscovered0;
  unsigned _satDiscoveredAfterNGM;
  unsigned _satDiscoveredIterativelyAfterNGM;
  unsigned _satDiscoveryIterationCnt;


  void reportResults();
};

}

#endif // __EPRRestoringScanner__
