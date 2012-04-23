
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

TEST_FUN(preprapiPredEqDiscovery)
{
  Problem::PreprocessingOptions popts;
  popts.equivalenceDiscovery = Problem::ED_PREDICATE_EQUIVALENCES;

  assertEarlyPreprocActive(popts, false, "fof(a,axiom, p(X) | ~q(X) ). fof(a,axiom, p(a) & q(a)).");
  assertEarlyPreprocActive(popts, true, "fof(a,axiom, p(X) | ~q(X) ). fof(a,axiom, ~p(X) | q(X) ). fof(a,axiom, p(a) & q(a)).");

  popts.equivalenceDiscoverySatConflictLimit = 3;
  assertEarlyPreprocActive(popts, true, "fof(a,axiom, p(X) | ~q(X) ). fof(a,axiom, ~p(X) | q(X) ). fof(a,axiom, p(a) & q(a)).");
  assertEarlyPreprocActive(popts, false, "fof(a,axiom, p(X) | ~q(X) ). fof(a,axiom, ?[X]: (~p(X) | q(X)) ). fof(a,axiom, p(a) & q(a)).");

  assertEarlyPreprocActive(popts, false, "fof(a,axiom, p(a,X) | ~q(a,X) ). fof(a,axiom, ~p(a,X) | q(a,X) ). fof(a,axiom, p(a,b) & q(a,b)).");
  popts.equivalenceDiscovery = Problem::ED_ATOM_EQUIVALENCES;
  assertEarlyPreprocActive(popts, true, "fof(a,axiom, p(a,X) | ~q(a,X) ). fof(a,axiom, ~p(a,X) | q(a,X) ). fof(a,axiom, p(a,b) & q(a,b)).");
}

TEST_FUN(preprapiPredDefDiscovery)
{
  Problem::PreprocessingOptions popts;

  const char* prb = "fof(a,axiom, p(X) | ~q(a) ). fof(a,axiom, ~p(X) | q(a) ). fof(a,axiom, p(b) & q(b)).";

  popts.equivalenceDiscovery = Problem::ED_PREDICATE_EQUIVALENCES;
  assertEarlyPreprocActive(popts, false, prb);
  popts.equivalenceDiscovery = Problem::ED_PREDICATE_DEFINITIONS;
  assertEarlyPreprocActive(popts, true, prb);
  popts.equivalenceDiscovery = Problem::ED_ATOM_EQUIVALENCES;
  assertEarlyPreprocActive(popts, true, prb);
}

TEST_FUN(preprapiFormulaEqDiscovery)
{
  Problem::PreprocessingOptions popts;

  const char* prb = "fof(a,axiom, (p(c)&q(c)) | ~(p(d)&q(d)) ). fof(a,axiom, ~(p(c)&q(c)) | (p(d)&q(d)) ). fof(a,axiom, p(a) & q(a)).";

  popts.equivalenceDiscovery = Problem::ED_ATOM_EQUIVALENCES;
  assertEarlyPreprocActive(popts, false, prb);
  popts.equivalenceDiscovery = Problem::ED_FORMULA_EQUIVALENCES;
  assertEarlyPreprocActive(popts, true, prb);
}

TEST_FUN(preprapiRestrictedPredEqDiscovery)
{
  FormulaBuilder api;
  Var xVar = api.var("X");
  Term x = api.varTerm(xVar);
  Predicate p = api.predicate("p",1, api.defaultSort());
  Predicate q = api.predicate("q",1, api.defaultSort());

  Formula pX = api.formula(p, x);
  Formula qX = api.formula(q, x);

  Problem::PreprocessingOptions popts;
  popts.equivalenceDiscovery = Problem::ED_PREDICATE_EQUIVALENCES;
  popts.restrictPredicateEquivalenceDiscovery(1, &pX, 1, &qX);

  assertEarlyPreprocActive(popts, false, "fof(a,axiom, p(X) | ~q(X) ). fof(a,axiom, p(a) & q(a)).");
  assertEarlyPreprocActive(popts, true, "fof(a,axiom, p(X) | ~q(X) ). fof(a,axiom, ~p(X) | q(X) ). fof(a,axiom, p(a) & q(a)).");
  assertEarlyPreprocActive(popts, false, "fof(a,axiom, p(X) | ~r(X) ). fof(a,axiom, ~p(X) | r(X) ). fof(a,axiom, p(a) & r(a)).");
}


TEST_FUN(preprapiTopLevelFlatten)
{
  Problem::PreprocessingOptions popts;
  popts.flatteningTopLevelConjunctions = true;

  assertEarlyPreprocActive(popts, true, "fof(a,axiom, p & q).");
  assertEarlyPreprocActive(popts, false, "fof(a,axiom, ?[X]: (p(X) & q(X))).");
}

TEST_FUN(preprapiBDDSweeping)
{
  Problem::PreprocessingOptions popts;
  popts.aigBddSweeping = true;

  assertEarlyPreprocActive(popts, true, "fof(a,axiom, p & (q | (r | ((p & b) | ~q))) & (a => a1) & (a1=>a2) & (a2=>b) & a ).");
  assertEarlyPreprocActive(popts, false, "fof(a,axiom, p(X) & ?[X]: (p(X) & q(X))).");
}

TEST_FUN(preprapiAIGInlining)
{
  Problem::PreprocessingOptions popts;
  popts.aigInlining = true;

  assertEarlyPreprocActive(popts, true, "fof(a,axiom, p & (q | (r | ((p & b) | ~q))) & (a => a1) & (a1=>a2) & (a2=>b) & a ).");
  assertEarlyPreprocActive(popts, false, "fof(a,axiom, p(X) & ?[X]: (p(X) & q(X))).");
}

TEST_FUN(preprapiAIGDefIntroduction)
{
  Problem::PreprocessingOptions popts;
  popts.aigDefinitionIntroduction = true;

  assertEarlyPreprocActive(popts, true, "fof(a,axiom, p1 | (a & b)).fof(a,axiom, p2 | (a & b)).fof(a,axiom, p3 | (a & b)).fof(a,axiom, p4 | (a & b)).");
  assertEarlyPreprocActive(popts, false, "fof(a,axiom, p(X) & ?[X]: (p(X) & q(X))).");
}


