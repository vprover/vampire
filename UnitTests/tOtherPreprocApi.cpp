
#include <iostream>
#include <sstream>
#include <map>

#include "Api/FormulaBuilder.hpp"
#include "Api/Problem.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/Term.hpp"

#include "Test/TestUtils.hpp"
#include "Test/UnitTesting.hpp"

#define UNIT_ID preprapi
UT_CREATE;

using namespace std;
using namespace Api;
using namespace Test;


void assertEarlyPreprocActive(Problem::PreprocessingOptions popts, bool shouldPerform, string prbStr)
{
  //default opts, we assume the preprocessing is disabled there
  Problem::PreprocessingOptions popts0;
  popts0.mode = Problem::PM_EARLY_PREPROCESSING;
  popts0.unusedPredicateDefinitionRemoval = false;

  popts.mode = Problem::PM_EARLY_PREPROCESSING;
  popts.unusedPredicateDefinitionRemoval = false;

  Problem prb;
  stringstream stm(prbStr);
  prb.addFromStream(stm);


  Problem prb_def = prb.preprocess(popts0);
  Kernel::Formula* f_def = TestUtils::getUniqueFormula(prb_def);
  size_t def_sz = prb_def.size();

  Problem prb_pp = prb.preprocess(popts);
  Kernel::Formula* f_pp = TestUtils::getUniqueFormula(prb_pp);
  size_t pp_sz = prb_pp.size();

  if(shouldPerform) {
    ASS_REP(f_def!=f_pp || def_sz!=pp_sz, *f_pp);
  }
  else {
    ASS_REP2(f_def==f_pp && def_sz==pp_sz, *f_def, *f_pp);
  }
}

TEST_FUN(preprapiPredIndexing)
{
  Problem::PreprocessingOptions popts;
  popts.predicateIndexIntroduction = true;

  assertEarlyPreprocActive(popts, true, "fof(a,axiom, p(a,X)). fof(a,axiom, p(a,b)).");
  assertEarlyPreprocActive(popts, false, "fof(a,axiom, p(a,X)). fof(a,axiom, p(b,b)).");
}

TEST_FUN(preprapiTopLevelFlatten)
{
  Problem::PreprocessingOptions popts;
  popts.flatteningTopLevelConjunctions = true;

  assertEarlyPreprocActive(popts, true, "fof(a,axiom, p & q).");
  assertEarlyPreprocActive(popts, false, "fof(a,axiom, ?[X]: (p(X) & q(X))).");
}


