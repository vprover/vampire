
/*
 * File PreprocessingEvaluator.cpp.
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
 * @file PreprocessingEvaluator.cpp
 * Implements class PreprocessingEvaluator.
 */

#include "Lib/DHSet.hpp"
#include "Lib/Environment.hpp"
#include "Lib/ScopedPtr.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Term.hpp"

#include "Shell/CommandLine.hpp"
#include "Shell/Options.hpp"
#include "Shell/Preprocess.hpp"
#include "Shell/UIHelper.hpp"

#include "PreprocessingEvaluator.hpp"

namespace VUtils
{

int PreprocessingEvaluator::perform(int argc, char** argv)
{
  CALL("PreprocessingEvaluator::perform");

  env.options->setTheoryAxioms(false);
  CommandLine cl(argc-1,argv+1);
  cl.interpret(*env.options);

  PROCESS_TRACE_SPEC_STRING(env.options->traceSpecString());
  env.options->enableTracesAccordingToOptions();

  _parsing.reset();
  _parsing.start();
  ScopedPtr<Problem> prb(UIHelper::getInputProblem(*env.options));
  _parsing.stop();

  _preproc.reset();
  _preproc.start();
  Preprocess pr(*env.options);
  pr.preprocess(*prb);
  _preproc.stop();

  printStatistics(*prb);

  return 0;
}

void PreprocessingEvaluator::printStatistics(Problem& prb)
{
  CALL("PreprocessingEvaluator::printStatistics");

  DHSet<Literal*> posLits;

  unsigned clauseCnt = 0;
  unsigned atomCnt = 0;
  unsigned distinctAtomCnt = 0;

  UnitList::Iterator uit(prb.units());
  while(uit.hasNext()) {
    Clause* cl = static_cast<Clause*>(uit.next());
    ASS(cl->isClause());
    clauseCnt++;
    Clause::Iterator cit(*cl);
    while(cit.hasNext()) {
      Literal* lit = cit.next();
      atomCnt++;
      if(posLits.insert(Literal::positiveLiteral(lit))) {
	distinctAtomCnt++;
      }
    }
  }
  cout<< _parsing.elapsedDeciseconds() << "\t"
      << _preproc.elapsedDeciseconds() << "\t"
      << clauseCnt << "\t"
      << atomCnt << "\t"
      << distinctAtomCnt;
}

}
