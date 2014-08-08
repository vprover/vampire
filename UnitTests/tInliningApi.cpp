
#include <iostream>
#include <sstream>
#include <map>

#include "Api/FormulaBuilder.hpp"
#include "Api/Problem.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/Term.hpp"

#include "Test/TestUtils.hpp"
#include "Test/UnitTesting.hpp"

#define UNIT_ID inlapi
UT_CREATE;

using namespace std;
using namespace Api;
using namespace Test;


void assertInliningActivation(Problem::InliningMode mode, bool shouldPerform, vstring prbStr)
{
  Problem::PreprocessingOptions popts;
  popts.mode = Problem::PM_EARLY_PREPROCESSING;
  popts.unusedPredicateDefinitionRemoval = false;

  Problem prb;
  vstringstream stm(prbStr);
  prb.addFromStream(stm);


  popts.predicateDefinitionInlining = Problem::INL_OFF;
  Problem prb_pp = prb.preprocess(popts);
  Kernel::Formula* f_pp = TestUtils::getUniqueFormula(prb_pp);

  popts.predicateDefinitionInlining = mode;
  Problem prb_inl = prb.preprocess(popts);
  Kernel::Formula* f_inl = TestUtils::getUniqueFormula(prb_inl);

  if(shouldPerform) {
    ASS_REP(f_pp!=f_inl, *f_inl);
  }
  else {
    ASS_REP2(f_pp==f_inl, *f_pp, *f_inl);
  }
}

TEST_FUN(inlapiFullInlining)
{
  assertInliningActivation(Problem::INL_ON, true, "fof(a,axiom,p(X) <=> (q(X) | r(X))). fof(b,axiom,p(a) | p(b)).");
  assertInliningActivation(Problem::INL_ON, true, "fof(a,axiom,p(X) <=> q(X,c)). fof(b,axiom,p(a) | p(b)).");
  assertInliningActivation(Problem::INL_ON, true, "fof(a,axiom,p(X) <=> (q(X) | r(X))). fof(b,axiom,p(a)).");
  assertInliningActivation(Problem::INL_ON, true, "fof(a,axiom,p(X) <=> q(f(X),c)). fof(b,axiom,p(a) | p(b)).");
}

TEST_FUN(inlapiNongrowingInlining)
{
  assertInliningActivation(Problem::INL_NON_GROWING, false, "fof(a,axiom,p(X) <=> (q(X) | r(X))). fof(b,axiom,p(a) | p(b)).");
  assertInliningActivation(Problem::INL_NON_GROWING, true, "fof(a,axiom,p(X) <=> q(X,c)). fof(b,axiom,p(a) | p(b)).");
  assertInliningActivation(Problem::INL_NON_GROWING, true, "fof(a,axiom,p(X) <=> (q(X) | r(X))). fof(b,axiom,p(a)).");
  assertInliningActivation(Problem::INL_NON_GROWING, false, "fof(a,axiom,p(X) <=> q(f(X),c)). fof(b,axiom,p(a) | p(b)).");
}


