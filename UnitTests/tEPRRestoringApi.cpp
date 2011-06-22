
#include <iostream>
#include <sstream>
#include <map>

#include "Api/FormulaBuilder.hpp"
#include "Api/Problem.hpp"

#include "Lib/Environment.hpp"
#include "Lib/DHSet.hpp"

#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"

#include "Test/UnitTesting.hpp"

#define UNIT_ID epr
UT_CREATE;

using namespace std;
using namespace Api;



TEST_FUN(eprPDInlining)
{
  try {
    FormulaBuilder api;

    Var xv = api.var("Var");
    Var yv = api.var("Var2");
    Function cSym=api.function("c",0);
    Term x = api.varTerm(xv);
    Term y = api.varTerm(yv);
    Term c = api.term(cSym);
    Predicate p=api.predicate("p",1);
    Predicate q=api.predicate("q",2);

    Formula fpx=api.formula(p,x);
    Formula fqyx=api.formula(q,y,x);
    Formula fqyc=api.formula(q,y,c);
    Formula fqycOqyx=api.formula(FormulaBuilder::OR, fqyc, fqyx);
    Formula fFyqycOqyx=api.formula(FormulaBuilder::FORALL, yv, fqycOqyx);
    Formula fdef=api.formula(FormulaBuilder::IFF, fpx, fFyqycOqyx);
    AnnotatedFormula afDef=api.annotatedFormula(fdef,FormulaBuilder::AXIOM, "pd");

    Formula fpy=api.formula(p,y);
    AnnotatedFormula afpy=api.annotatedFormula(fpy,FormulaBuilder::AXIOM, "py");

    cout<<endl<<"FOF:"<<endl;
    cout<<afDef<<endl;
    cout<<afpy<<endl;

    Problem prb;
    prb.addFormula(afDef);
    prb.addFormula(afpy);

    OutputOptions::setTffFormulas(true);

    Problem sprb=prb.skolemize(0, true, Problem::INL_ON, false);
    cout<<"Skolemized:"<<endl;
    AnnotatedFormulaIterator afit=sprb.formulas();
    while(afit.hasNext()) {
      cout<<afit.next()<<endl;
    }

    Problem cprb=prb.clausify(0, true, Problem::INL_ON, false);
    cout<<"CNF:"<<endl;
    afit=cprb.formulas();
    while(afit.hasNext()) {
      cout<<afit.next()<<endl;
    }
    OutputOptions::setTffFormulas(false);
  } catch (ApiException e) {
    cout<<"Exception: "<<e.msg()<<endl;
    throw;
  }
}

TEST_FUN(eprPDInlining2)
{
  try {
    Problem prb;
//    stringstream stm(
//	"fof(memoryEquality,axiom,"
//	"    (toy_EXP_9(VarCurr) <=> (![A] : ((address(A) => (![B] : (((less_5(B) & (~less_0(B))) => (toy_mem_array(VarCurr,A,B) <=> toy_mem2_array(VarCurr,A,B)))) ))) )))."
//	"fof(writeUnaryOperator,axiom,"
//	"   ((~toy_EXP_41(VarCurr)) <=> toy_EXP_9(VarCurr)))."
//	"fof(writeUnaryOperator,axiom,"
//	"   ((~toy_assume_memory_correspondence_fs_assert_reachable(VarCurr)) <=> toy_EXP_41(VarCurr)))."
//	"fof(addAssertion,conjecture,"
//	"   (![VarCurr] : ((reachableState(VarCurr) => toy_assume_memory_correspondence_fs_assert_reachable(VarCurr))) )).");
    stringstream stm(
	"fof(a,axiom, p <=> r). fof(a,hypothesis, p <=> (q|s)).fof(a,axiom, r => u).");
    prb.addFromStream(stm);

    cout<<endl<<"FOF:"<<endl;
    AnnotatedFormulaIterator afit=prb.formulas();
    while(afit.hasNext()) {
      cout<<afit.next()<<endl;
    }

    Problem iprb=prb.inlinePredicateDefinitions();
    cout<<"Inlined:"<<endl;
    afit=iprb.formulas();
    while(afit.hasNext()) {
      cout<<afit.next()<<endl;
    }

    Problem::PreprocessingOptions opts;
    opts.mode = Problem::PM_EARLY_PREPROCESSING;
    opts.unusedPredicateDefinitionRemoval = false;
    opts.traceInlining = true;
    opts.predicateDefinitionInlining = Problem::INL_AXIOMS_ONLY;
    iprb=prb.preprocess(opts);
    cout<<"Inlined (axioms only):"<<endl;
    afit=iprb.formulas();
    while(afit.hasNext()) {
      cout<<afit.next()<<endl;
    }
  } catch (ApiException e) {
    cout<<"Exception: "<<e.msg()<<endl;
    throw;
  }
}

TEST_FUN(eprEPRRestoringInlining)
{
  try {
    OutputOptions::setTffFormulas(true);

    Problem prb;
    stringstream stm(
	"fof(a,axiom, p <=> (r(a)|q)). fof(b,hypothesis, p). fof(c,hypothesis, ~p). fof(d,axiom, r(X) <=> ![Y] : z(Y,a))."
	"fof(e,axiom, q <=> (s|t)).");
    prb.addFromStream(stm);

    cout<<endl<<"FOF:"<<endl;
    prb.output(cout);

    Problem iprb=prb.inlinePredicateDefinitions(Problem::INL_EPR_RESTORING).removeUnusedPredicateDefinitions();
    cout<<"Inlined:"<<endl;
    iprb.output(cout);

    Problem::PreprocessingOptions opts;
    opts.mode = Problem::PM_SKOLEMIZE;
    opts.predicateDefinitionInlining = Problem::INL_EPR_RESTORING;
    opts.traceInlining = true;
    iprb = prb.preprocess(opts);
    cout<<"Skolemized:"<<endl;
    iprb.output(cout);
    OutputOptions::setTffFormulas(false);
  } catch (ApiException e) {
    cout<<"Exception: "<<e.msg()<<endl;
    throw;
  }
}

TEST_FUN(eprEPRRestoringInliningCycles)
{
  try {
    Problem prb;
    stringstream stm(
	"fof(d,axiom, r(X) <=> ![Y] : z(Y))."
	"fof(d,axiom, z(X) <=> ![Y] : w(Y))."
	"fof(d,axiom, w(X) <=> ![Y] : r(Y))."
	"fof(a,axiom, p <=> (r(a)|q)).");
    prb.addFromStream(stm);

    cout<<endl<<"FOF:"<<endl;
    prb.output(cout);

    Problem iprb=prb.inlinePredicateDefinitions(Problem::INL_EPR_RESTORING).removeUnusedPredicateDefinitions();
    cout<<"Inlined:"<<endl;
    iprb.output(cout);

    Problem::PreprocessingOptions opts;
    opts.mode = Problem::PM_SKOLEMIZE;
    opts.predicateDefinitionInlining = Problem::INL_EPR_RESTORING;
    opts.traceInlining = true;
    iprb = prb.preprocess(opts);
    cout<<"Skolemized:"<<endl;
    iprb.output(cout);
  } catch (ApiException e) {
    cout<<"Exception: "<<e.msg()<<endl;
    throw;
  }
}

TEST_FUN(eprEqPropagation)
{
  try {
    Problem prb;
    stringstream stm(
	"fof(d,axiom, X!=Y | p(X,Y)).");
    prb.addFromStream(stm);

    cout<<endl<<"FOF:"<<endl;
    prb.output(cout);

    Problem::PreprocessingOptions opts;
    opts.mode = Problem::PM_EARLY_PREPROCESSING;
    opts.predicateDefinitionInlining = Problem::INL_OFF;
    opts.unusedPredicateDefinitionRemoval = false;
    opts.variableEqualityPropagation = true;
    opts.traceVariableEqualityPropagation = true;
    Problem iprb = prb.preprocess(opts);
    cout<<"Propagated:"<<endl;
    iprb.output(cout);
  } catch (ApiException e) {
    cout<<"Exception: "<<e.msg()<<endl;
    throw;
  }
}

TEST_FUN(eprAsymReplacement)
{
  try {
    Problem prb;
    stringstream stm(
	"fof(a1,axiom, p(X) <=> r). fof(a2,hypothesis, p(X) => (q|s)). fof(a3,axiom, ~r => p(X)). fof(a4,axiom, p(X)).");
    prb.addFromStream(stm);

    cout<<endl<<"FOF:"<<endl;
    prb.output(cout);

    FormulaBuilder api;

    Var xv = api.var("Var");
    Function cSym=api.function("c",0);
    Function dSym=api.function("d",0);
    Term x = api.varTerm(xv);
    Term c = api.term(cSym);
    Term d = api.term(dSym);
    Predicate p=api.predicate("p",1);
    Predicate r=api.predicate("r",0);
    Predicate q=api.predicate("q",2);

    Formula fr=api.formula(r);
    Formula fpx=api.formula(p,x);
    Formula fpc=api.formula(p,c);
    Formula fqxx=api.formula(q,x,x);
    Formula fqcx=api.formula(q,c,x);
    Formula fqdd=api.formula(q,d,d);
    Formula fOr=api.formula(FormulaBuilder::OR, fpx, fpc);
    Formula ft=api.trueFormula();


    Problem iprb=prb.performAsymetricRewriting(fpx, fOr, ft);
    cout<<"Inlined (px, pxOpc, $true, 0):"<<endl;
    iprb.output(cout);

    iprb=prb.performAsymetricRewriting(fpx, fpc, fqxx, fqcx);
    cout<<"Inlined (px, pc, qxx, qcx):"<<endl;
    iprb.output(cout);

    Formula lhsA[] = {fpx,api.negation(fr)};
    Formula rhsPosA[] = {fOr,fqdd};
    Formula rhsNegA[] = {ft,fqdd};
    Formula rhsDblA[] = {fqxx,fqdd};
    iprb=prb.performAsymetricRewriting(2, lhsA, rhsPosA, rhsNegA, rhsDblA);
    cout<<"Inlined arr:"<<endl;
    iprb.output(cout);

    Problem::PreprocessingOptions opts;
    opts.mode = Problem::PM_EARLY_PREPROCESSING;
    opts.unusedPredicateDefinitionRemoval = false;
    opts.addAsymmetricRewritingRule(fpx, fOr, ft, fqxx);
    opts.addAsymmetricRewritingRule(api.negation(fr), fqdd, fqdd, fqdd);

    //test the copy constructor and assignment of PreprocessingOptions
    Problem::PreprocessingOptions opts1(opts);
    opts = opts1;

    iprb=prb.preprocess(opts);
    cout<<"Inlined by preprocess:"<<endl;
    iprb.output(cout);

  } catch (ApiException e) {
    cout<<"Exception: "<<e.msg()<<endl;
    throw;
  }
}


TEST_FUN(eprUPDR)
{
  try {
    Problem prb;
    stringstream stm(
//	"fof(a,axiom, p <=> (r|s&t)). fof(a,hypothesis, p). fof(a,axiom, r => ~s)."
	 "fof(addBitVectorEquality,axiom,"
	    "(exp_17(VarCurr) <=> (![B] : (((less_5(B) & (~less_0(B))) => (outp(VarCurr,B) <=> outp2(VarCurr,B)))) )))."
	 "fof(addAssertion,conjecture,"
	   "(![VarCurr] : ((~exp_17(VarCurr))) ))."
	 "fof(addAssertion,hypothesis,"
	   "((less_5(B) & less_0(B)) <=> (outp(VarCurr,B) <=> outp2(VarCurr,B)) ))."
	);
    prb.addFromStream(stm);

    cout<<endl<<"FOF:"<<endl;
    AnnotatedFormulaIterator afit=prb.formulas();
    while(afit.hasNext()) {
      cout<<afit.next()<<endl;
    }

    Problem iprb=prb.removeUnusedPredicateDefinitions();
    cout<<"After updr:"<<endl;
    afit=iprb.formulas();
    while(afit.hasNext()) {
      cout<<afit.next()<<endl;
    }
  } catch (ApiException e) {
    cout<<"Exception: "<<e.msg()<<endl;
    throw;
  }
}

TEST_FUN(eprUPDRBuiltInPreds)
{
  try {
    Problem prb;
    stringstream stm(
	"fof(a,axiom, p <=> (r|s&t)). fof(a,hypothesis, p). fof(a,axiom, r => ~s). fof(a,axiom, a). fof(a,axiom, b)."
	);
    prb.addFromStream(stm);

    cout<<endl<<"FOF:"<<endl;
    AnnotatedFormulaIterator afit=prb.formulas();
    while(afit.hasNext()) {
      cout<<afit.next()<<endl;
    }

    Predicate bPred = Predicate(env.signature->addPredicate("b", 0));

    Problem::PreprocessingOptions opts;
    opts.mode = Problem::PM_EARLY_PREPROCESSING;
    opts.unusedPredicateDefinitionRemoval = true;
    opts.addBuiltInPredicate(bPred);

    Problem iprb=prb.preprocess(opts);
    cout<<"After updr:"<<endl;
    afit=iprb.formulas();
    while(afit.hasNext()) {
      cout<<afit.next()<<endl;
    }
  } catch (ApiException e) {
    cout<<"Exception: "<<e.msg()<<endl;
    throw;
  }
}

TEST_FUN(eprEPRSkolem)
{
  try {
    FormulaBuilder api;

    Var xv = api.var("Var");
    Var yv = api.var("Var2");
    Function cSym=api.function("c",0);
    Term x = api.varTerm(xv);
    Term y = api.varTerm(yv);
    Term c = api.term(cSym);
    Predicate p=api.predicate("p",1);
    Predicate q=api.predicate("q",2);

    Formula fpx=api.formula(p,x);
    Formula fqyx=api.formula(q,y,x);
    Formula fqyc=api.formula(q,y,c);
    Formula fqycOqyx=api.formula(FormulaBuilder::OR, fqyc, fqyx);
    Formula fFyqycOqyx=api.formula(FormulaBuilder::FORALL, yv, fqycOqyx);
    Formula fdef=api.formula(FormulaBuilder::IFF, fpx, fFyqycOqyx);
    AnnotatedFormula afDef=api.annotatedFormula(fdef,FormulaBuilder::AXIOM, "pd");

    Formula fNpc=api.negation(api.formula(p,c));
    AnnotatedFormula afNpc=api.annotatedFormula(fNpc,FormulaBuilder::AXIOM, "pc");

    Problem prb;
    prb.addFormula(afDef);
    prb.addFormula(afNpc);

    OutputOptions::setTffFormulas(true);

    cout<<endl<<"FOF:"<<endl;
    prb.output(cout);

    Problem::PreprocessingOptions opts;
    opts.mode = Problem::PM_EARLY_PREPROCESSING;
    opts.unusedPredicateDefinitionRemoval = false;
    opts.eprSkolemization = true;
    opts.traceEPRSkolemization = true;

    Problem pprb=prb.preprocess(opts);
    cout<<"Preprocessed:"<<endl;
    pprb.output(cout);
    OutputOptions::setTffFormulas(false);

    opts.mode = Problem::PM_SKOLEMIZE;
    opts.traceEPRSkolemization = false;
    Problem sprb=prb.preprocess(opts);
    cout<<"Skolemized:"<<endl;
    sprb.output(cout);


  } catch (ApiException e) {
    cout<<"Exception: "<<e.msg()<<endl;
    throw;
  }
}

TEST_FUN(eprPDMerging)
{
  try {
    Problem prb;
    stringstream stm(
	"fof(a1,axiom, p(X) <=> (q(a) | q(X)) ). fof(a2,axiom, r(X) <=> (q(a) | q(X)) )."
	"fof(a,axiom, r(a) | p(a)).");
    prb.addFromStream(stm);

    cout<<endl<<"FOF:"<<endl;
    prb.output(cout);

    Problem::PreprocessingOptions opts;
    opts.mode = Problem::PM_EARLY_PREPROCESSING;
    opts.unusedPredicateDefinitionRemoval = false;
    opts.tracePredicateDefinitionMerging = true;
    opts.predicateDefinitionMerging = true;
    Problem iprb=prb.preprocess(opts);
    cout<<"Merged:"<<endl;
    iprb.output(cout);
  } catch (ApiException e) {
    cout<<"Exception: "<<e.msg()<<endl;
    throw;
  }
}

