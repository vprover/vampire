
/*
 * File DPTester.cpp.
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
 * @file DPTester.cpp
 * Implements class DPTester.
 */

#include "Debug/Tracer.hpp"

#include "DP/SimpleCongruenceClosure.hpp"

#include "Lib/Environment.hpp"
#include "Lib/ScopedPtr.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Problem.hpp"

#include "Shell/Options.hpp"
#include "Shell/Preprocess.hpp"
#include "Shell/UIHelper.hpp"

#include "DPTester.hpp"

namespace VUtils
{


int DPTester::perform(int argc, char** argv)
{
  CALL("DPTester::perform");

  vstring fname = argv[2];
  env.options->setInputFile(fname);

  cout << "solving "<<fname<<endl;

  env.options->setUnusedPredicateDefinitionRemoval(false);
  ScopedPtr<Problem> prb(UIHelper::getInputProblem(*env.options));

  Preprocess(*env.options).preprocess(*prb);

  LiteralStack lits;

  ClauseIterator cit = prb->clauseIterator();
  while(cit.hasNext()) {
    Clause* cl = cit.next();
    if(cl->length()!=1) {
      USER_ERROR("non-unit clause: "+cl->toString());
    }
    Literal* lit = (*cl)[0];
    lits.push(lit);
    cout << (*lit) << endl;
  }

  ScopedPtr<DecisionProcedure> dp(new SimpleCongruenceClosure());

  dp->addLiterals(pvi(LiteralStack::Iterator(lits)));

  switch(dp->getStatus()) {
  case DecisionProcedure::SATISFIABLE:
    cout << "SAT" << endl;
    break;
  case DecisionProcedure::UNSATISFIABLE:
    cout << "UNSAT" << endl;
    break;
  case DecisionProcedure::UNKNOWN:
    cout << "UNKNOWN" << endl;
    break;
  }


  return 0;
}


}
