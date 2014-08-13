
#include <iostream>
#include <sstream>
#include <map>

#include "Api/FormulaBuilder.hpp"
#include "Api/Problem.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/Term.hpp"

#include "Test/TestUtils.hpp"
#include "Test/UnitTesting.hpp"

#define UNIT_ID preprStagesApi
UT_CREATE;

using namespace std;
using namespace Api;
using namespace Test;



TEST_FUN(psaFixedPoint)
{
  vstring testPrb =
      "fof(a,axiom, p(X,Y,Z)<=>q(X,Y) )."
      "fof(a,axiom, p(X,Y,a)<=>r(X) )."
      "fof(a,axiom, p(X,a,a)<=>s )."
      "fof(a,axiom, p(a,a,a) ).";

  Problem prb;
  vostringstream stm(testPrb);
  prb.addFromStream(stm);

  Problem prb1 = prb.preprocessInStages("rc=0:ret=formula_count:m=early_preprocessing:pdi=on:updr=off");
  Problem prb2 = prb.preprocessInStages("rc=2:ret=formula_count:m=early_preprocessing:pdi=on:updr=off");

  ASS_NEQ(TestUtils::getUniqueFormula(prb1), TestUtils::getUniqueFormula(prb2));
}


