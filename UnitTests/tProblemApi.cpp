
#include <iostream>
#include <sstream>
#include <map>

#include "Api/FormulaBuilder.hpp"
#include "Api/Problem.hpp"

#include "Kernel/Term.hpp"

#include "Test/UnitTesting.hpp"

#define UNIT_ID papi
UT_CREATE;

using namespace std;
using namespace Api;



TEST_FUN(papi1)
{
  Problem prb;
  stringstream stm("cnf(a,axiom,p(X) | q(Y) | q(X)).");

  prb.addFromStream(stm);

  AnnotatedFormulaIterator fit=prb.formulas();

  ASS(fit.hasNext());
  AnnotatedFormula af=fit.next();
  ASS(!fit.hasNext());

  int i=0;
  StringIterator sit=af.freeVars();
  while(sit.hasNext()) {
    sit.next();
    i++;
  }
  ASS_EQ(i,2);

  sit=af.freeVars();
  DHSet<string> sset;
  sset.loadFromIterator(sit);
  ASS_EQ(sset.size(), 2);

}

TEST_FUN(papiClausifySmall)
{
  try {
    FormulaBuilder api;

    Var xv = api.var("Var");
    Term x = api.varTerm(xv);
    Predicate p=api.predicate("p",1);
    Predicate q=api.predicate("q",0);

    Formula fpx=api.formula(p,x);
    Formula fq=api.formula(q);
    Formula fQpx=api.formula(FormulaBuilder::FORALL, xv, fpx);
    Formula fQpxOq=api.formula(FormulaBuilder::OR, fQpx, fq);

    AnnotatedFormula af=api.annotatedFormula(fQpxOq,FormulaBuilder::CONJECTURE, "conj1");
    Problem prb;
    prb.addFormula(af);
    prb.output(cout);

    Problem cprb=prb.clausify(0,false,Problem::INL_OFF,false);
    cprb.output(cout);

  } catch (ApiException e) {
    cout<<"Exception: "<<e.msg()<<endl;
    throw;
  }
}


TEST_FUN(papiClausify)
{
  try {
    FormulaBuilder api;

    Var xv = api.var("Var");
    Var yv = api.var("Var2");
    Term x = api.varTerm(xv);
    Term y = api.varTerm(yv);
    Predicate p=api.predicate("p",1);
    Predicate q=api.predicate("q",0);

    Formula fpx=api.formula(p,x);
    Formula fpy=api.formula(p,y);
    Formula fq=api.formula(q);
    Formula fpxOq=api.formula(FormulaBuilder::OR, fpx, fq);
    Formula fFpxOq=api.formula(FormulaBuilder::FORALL, xv, fpxOq);
    Formula fpyAFpxOq=api.formula(FormulaBuilder::AND, fpy, fFpxOq);

    AnnotatedFormula af=api.annotatedFormula(fpyAFpxOq,FormulaBuilder::CONJECTURE, "abc123");

    cout<<endl<<"FOF:"<<endl;
    cout<<af<<endl;

    Problem prb;
    prb.addFormula(af);

    Problem sprb=prb.skolemize(0,false,Problem::INL_OFF,false);
    cout<<"Skolemized:"<<endl;
    AnnotatedFormulaIterator afit=sprb.formulas();
    while(afit.hasNext()) {
      cout<<afit.next()<<endl;
    }

    Problem cprb=prb.clausify(0,false,Problem::INL_OFF,false);
    cout<<"CNF:"<<endl;
    afit=cprb.formulas();
    while(afit.hasNext()) {
      cout<<afit.next()<<endl;
    }

    cprb=sprb.clausify(0,false,Problem::INL_OFF,false);
    cout<<"CNF from skolemized:"<<endl;
    afit=cprb.formulas();
    while(afit.hasNext()) {
      cout<<afit.next()<<endl;
    }
  } catch (ApiException e) {
    cout<<"Exception: "<<e.msg()<<endl;
    throw;
  }
}

TEST_FUN(papiClausifyDefinitions)
{
  try {
    Problem prb;
    stringstream stm("fof(a,axiom,(? [X]: p(X)&p(a2)) | (p(b1)&p(b2)) | (p(c1)&p(c2)) | (p(d1)&p(d2)) | (p(e1)&p(e2))).");
    prb.addFromStream(stm);

    cout<<"Problem:"<<endl;
    AnnotatedFormulaIterator afit=prb.formulas();
    while(afit.hasNext()) {
      cout<<afit.next()<<endl;
    }

    Problem cprb = prb.clausify(4, true, Problem::INL_OFF, false);
    cout<<"Clausified, naming_threshold=4:"<<endl;
    afit=cprb.formulas();
    while(afit.hasNext()) {
      cout<<afit.next()<<endl;
    }
  } catch (ApiException e) {
    cout<<"Exception: "<<e.msg()<<endl;
    throw;
  }
}

TEST_FUN(papiSine)
{
  try {
    Problem prb;
    stringstream stm("fof(a1,axiom,a|b).fof(a2,axiom,b|c).fof(a3,axiom,b|d).fof(a4,axiom,d).fof(a4,axiom,d|e).fof(a5,conjecture,a).");
    prb.addFromStream(stm);
    Problem::PreprocessingOptions opts;
    opts.mode = Problem::PM_SELECTION_ONLY;
    opts.sineSelection = true;
    Problem prb1 = prb.preprocess(opts);
    prb1.output(cout, false);
    cout<<"------\n";
    opts.mode = Problem::PM_CLAUSIFY;
    opts.unusedPredicateDefinitionRemoval = false;
    opts.sineTolerance = 3;
    opts.traceClausification = true;
    Problem prb2 = prb.preprocess(opts);
    prb2.output(cout, false);

  } catch (ApiException& e) {
    cout<<"Exception: "<<e.msg()<<endl;
    throw;
  }
}

TEST_FUN(papiTff)
{
  Problem prb;
  stringstream stm("fof(a,axiom,p(X) | q(Y) | q(X)).");
  prb.addFromStream(stm);

  OutputOptions::setTffFormulas(true);
  prb.output(cout);
  OutputOptions::setTffFormulas(false);
}

TEST_FUN(papiEmptyPrb)
{
  FormulaBuilder fb;
  AnnotatedFormula af = fb.annotatedFormula(fb.trueFormula(), FormulaBuilder::CONJECTURE);
  Problem prb;
  prb.addFormula(af);
  Problem cprb = prb.clausify();
  cprb.output(cout);
}

TEST_FUN(papiPreprocOpts)
{
  Problem::PreprocessingOptions opts("m=early_preprocessing:ed=predicate_definitions:acr=on");
  opts.printOptionValues(cout);
}

