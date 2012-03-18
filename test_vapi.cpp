/**
 * @file test_vapi.cpp
 * Source of the test executable for the libvapi.
 */

#include <iostream>
#include <fstream>
#include <sstream>
#include <string>

#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Stack.hpp"
#include "Shell/Options.hpp"

#include "Api/FormulaBuilder.hpp"
#include "Api/Problem.hpp"
#include "Api/Tracing.hpp"


using namespace std;
using namespace Api;

void printProblem(Problem p)
{
  cout<<"____"<<endl;
  AnnotatedFormulaIterator fit=p.formulas();
  while(fit.hasNext()) {
    cout<<fit.next()<<endl;
  }
  cout<<"^^^^"<<endl;
}

void clausifyTest(const char* fname)
{
  ifstream fs(fname);
  Problem p;
  p.addFromStream(fs);

  Problem p2=p.clausify(8,true);
//  Problem p2=p.clausify(8,false);

  printProblem(p2);
}

void inlineTest(const char* fname)
{
  ifstream fs(fname);
  Problem p;
  p.addFromStream(fs);


#if 0
  {
    Problem::PreprocessingOptions m_PreprocessOpts;
    m_PreprocessOpts.predicateDefinitionInlining = Problem::INL_NON_GROWING;
    m_PreprocessOpts.mode = Problem::PM_EARLY_PREPROCESSING;
    m_PreprocessOpts.unusedPredicateDefinitionRemoval = false;
    m_PreprocessOpts.preserveEpr = false;
    m_PreprocessOpts.eprSkolemization = false;
    m_PreprocessOpts.predicateDefinitionMerging = false;
    m_PreprocessOpts.variableEqualityPropagation = false;

    p = p.preprocess(m_PreprocessOpts);
  }

  Problem::PreprocessingOptions m_PreprocessOpts;
  m_PreprocessOpts.unusedPredicateDefinitionRemoval = true;
  m_PreprocessOpts.preserveEpr = true;
  m_PreprocessOpts.eprSkolemization = false;
  m_PreprocessOpts.mode = Problem::PM_CLAUSIFY;
  m_PreprocessOpts.predicateDefinitionInlining = Problem::INL_EPR_RESTORING;
  m_PreprocessOpts.predicateDefinitionMerging = false;
  m_PreprocessOpts.predicateIndexIntroduction = false;
  m_PreprocessOpts.flatteningTopLevelConjunctions = true;
  m_PreprocessOpts.aigInlining = true;
  m_PreprocessOpts.aigBddSweeping = false;
  m_PreprocessOpts.aigDefinitionIntroduction = false;
  m_PreprocessOpts.predicateEquivalenceDiscovery = false;
  m_PreprocessOpts.predicateEquivalenceDiscoverySatConflictLimit = 0;

  p=p.preprocess(m_PreprocessOpts);
#else

  Problem::PreprocessingOptions m_PreprocessOpts;

  // default is 8; 32 showed good results on some of the examples but caused
  // generation of too many clauses in primnary_chain
  m_PreprocessOpts.namingThreshold = 8;
  m_PreprocessOpts.sineSelection = false;
  m_PreprocessOpts.sineTolerance = 0; // started with 1.5
  m_PreprocessOpts.sineDepthLimit = 0; // started with 2

  // do preliminary pre-processing in order to simplify the instance by
  // applying non-growing inlining
  m_PreprocessOpts.predicateDefinitionInlining = Problem::INL_NON_GROWING;
  m_PreprocessOpts.mode = Problem::PM_EARLY_PREPROCESSING;
  m_PreprocessOpts.unusedPredicateDefinitionRemoval = false;
  m_PreprocessOpts.preserveEpr = false;
  m_PreprocessOpts.eprSkolemization = false;
  m_PreprocessOpts.predicateDefinitionMerging = false;
  m_PreprocessOpts.variableEqualityPropagation = false;

  cout << "\nFirst stage of clausification... "<<endl;
  p = p.preprocess(m_PreprocessOpts);
 cout << "  ...done\n";

 return;

  // now perform the rest of pre-processing and clausification
  m_PreprocessOpts.unusedPredicateDefinitionRemoval = true;
  m_PreprocessOpts.preserveEpr = true;
  m_PreprocessOpts.eprSkolemization = true;
  m_PreprocessOpts.mode = Problem::PM_CLAUSIFY;
  m_PreprocessOpts.predicateDefinitionInlining = Problem::INL_EPR_RESTORING;
  m_PreprocessOpts.predicateDefinitionMerging = true;
  m_PreprocessOpts.predicateIndexIntroduction = true;
  m_PreprocessOpts.flatteningTopLevelConjunctions = true;
  m_PreprocessOpts.aigInlining = false;
  m_PreprocessOpts.aigBddSweeping = true;
  m_PreprocessOpts.aigDefinitionIntroduction = false;
  m_PreprocessOpts.predicateEquivalenceDiscovery = true;
  m_PreprocessOpts.predicateEquivalenceDiscoverySatConflictLimit = 0;
  m_PreprocessOpts.predicateEquivalenceDiscoveryPredicateEquivalencesOnly = false;
  m_PreprocessOpts.variableEqualityPropagation = true;

  cout << "\nSecond stage of clausification... "<<endl;
  p = p.preprocess(m_PreprocessOpts);
  cout << "  ...done\n";
#endif

  p.output(cout, true, false);
}

void assymmetricRewriteTest(const char* fname)
{
  Lib::env.options->set("protected_prefix","aaa__");

  ifstream fs(fname);
  Problem p;
  p.addFromStream(fs);

  FormulaBuilder api;
  Api::Sort bs = api.sort("bitindex_type");
  Api::Var v = api.var("B", bs);
  Api::Term vt = api.varTerm(v);

  Api::Predicate lf8 = api.predicate("aaa__lessFull_8", 1, &bs);
  Api::Predicate lf2 = api.predicate("aaa__lessFull_2", 1, &bs);
  Api::Predicate lf34 = api.predicate("aaa__lessFull_34", 1, &bs);
  Api::Predicate rng7 = api.predicate("aaa__range_7_0", 1, &bs);
  Api::Predicate rng1 = api.predicate("aaa__range_1_0", 1, &bs);
  Api::Predicate rng33 = api.predicate("aaa__range_33_0", 1, &bs);

  Api::Formula lhss[] = { api.formula(lf8, vt), api.formula(lf2, vt), api.formula(lf34, vt) };
  Api::Formula rhss[] = { api.formula(rng7, vt), api.formula(rng1, vt), api.formula(rng33, vt) };
  Api::Formula trues[] = { api.trueFormula(), api.trueFormula(), api.trueFormula() };

  Problem p2 = p.performAsymetricRewriting(3, lhss, rhss, trues, rhss);
  p2.output(cout, false, false);
}

void testSubst()
{
  try {
    FormulaBuilder api(true);

    Var xv = api.var("X"); // variable x
    Var yv = api.var("Y"); // variable y
    Term x =  api.varTerm(xv); // term x
    Term y =  api.varTerm(yv); // term y
    Function fun = api.function("f",1);
    Function cfun = api.function("c",0);
    Term c = api.term(cfun); // c
    Term fx = api.term(fun,x); // f(x)
    Term fy = api.term(fun,y); // f(y)
    Term fc = api.term(fun,c); // f(c)
    Term ffc = api.term(fun,fc); // f(f(c))
    Formula f1 = api.equality(fx,fy); // f(x) = f(y)
    Formula f2 = api.equality(fc,ffc); // f(c) = f(f(c))

    Formula f1neg = api.negation(f1);
    AnnotatedFormula af1neg = api.annotatedFormula(f1neg, FormulaBuilder::ASSUMPTION);
    AnnotatedFormula af1conj = api.annotatedFormula(f1neg, FormulaBuilder::CONJECTURE);

    cout<<f1neg.toString()<<endl;
    cout<<api.substitute(f1neg, xv, fx).toString()<<endl;
    cout<<api.substitute(api.substitute(f1neg, xv, fx), xv, fx).toString()<<endl;
    cout<<api.substitute(api.substitute(af1neg, xv, fx), xv, fx).toString()<<endl;
    cout<<api.substitute(api.substitute(fx, xv, fx), xv, fx).toString()<<endl;

    Formula f2neg = api.negation(f2);
    AnnotatedFormula af2neg = api.annotatedFormula(f2neg, FormulaBuilder::ASSUMPTION);
    AnnotatedFormula af2conj = api.annotatedFormula(f2neg, FormulaBuilder::CONJECTURE);
    cout<<af2neg.toString()<<endl;
    cout<<api.replaceConstant(af2neg, c, fx).toString()<<endl;
    cout<<api.replaceConstant(ffc, c, y).toString()<<endl;

  }
  catch (ApiException e)
  {
    cout<< "Exception: "<<e.msg()<<endl;
    throw;
  }
}

void asymRewritingTest()
{
  FormulaBuilder api(true);
  Predicate lf4 = api.predicate("lessFull_4", 1);
  Predicate l4 = api.predicate("less_4", 1);
  Var bv = api.var("B");
  Term b = api.varTerm(bv);
  Formula lf4b = api.formula(lf4, b);
  Formula l4b = api.formula(l4, b);

  Problem prb;
  prb.addFromStream(cin);

//  {
//    Problem::PreprocessingOptions opts;
//    opts.addAsymmetricRewritingRule(l4b, lf4b, lf4b, lf4b);
//    opts.mode = Problem::PM_EARLY_PREPROCESSING;
//    prb = prb.preprocess(opts);
//  }
  Problem::PreprocessingOptions opts;
  opts.addAsymmetricRewritingRule(lf4b, api.trueFormula(), l4b, l4b);
  opts.mode = Problem::PM_EARLY_PREPROCESSING;

  prb = prb.preprocess(opts);
  prb.output(cout);
}

void readAndFilterGlobalOpts(Stack<char*>& args) {
  Stack<char*>::StableDelIterator it(args);

  //skip the first item which is the executable name
  ALWAYS(it.hasNext());
  it.next();

  while(it.hasNext()) {
    string arg(it.next());
    if(arg=="-tr") {
      it.del();
      if(!it.hasNext()) {
	USER_ERROR("value for -tr option expected");
      }
      string traceStr(it.next());
      it.del();
      PROCESS_TRACE_SPEC_STRING(traceStr);
    }
    else if(arg=="-m") {
      it.del();
      if(!it.hasNext()) {
	USER_ERROR("value for -m option expected");
      }
      string memLimitStr = it.next();
      it.del();
      unsigned memLimit;
      if(!Int::stringToUnsignedInt(memLimitStr, memLimit)) {
	USER_ERROR("unsigned number expected as value of -m option");
      }
      env.options->setMemoryLimit(memLimit);
      Allocator::setMemoryLimit(env.options->memoryLimit()*1048576ul);
    }
    else {
      break;
    }
  }
}

int main(int argc, char* argv [])
{
  CALL("main");

  Stack<char*> args;
  args.loadFromIterator(getArrayishObjectIterator(argv, argc));
  readAndFilterGlobalOpts(args);

  if(args.size()==2) {
//    assymmetricRewriteTest(argv[1]);
    inlineTest(args[1]);
    return 0;
  }

  asymRewritingTest();
  Api::Tracing::pushTracingState();
  Api::Tracing::popTracingState();
  return 0;

  testSubst();

  FormulaBuilder api(true);

  Var xv = api.var("X"); // variable x
  Var yv = api.var("Y"); // variable y
  Term x =  api.varTerm(xv); // term x
  Term y =  api.varTerm(yv); // term y
  Function f = api.function("f",1);
  Term fx = api.term(f,x); // f(X)
  Term fy = api.term(f,y); // f(Y)
  Formula lhs = api.formula(FormulaBuilder::FORALL, xv, api.equality(fx,fy)); // f(X) = f(Y)
  Predicate p=api.predicate("p",3);
  Formula rhs = api.formula(FormulaBuilder::FORALL, xv, api.formula(p,x,fx,fy)); // p(X,f(X),f(Y))

  Formula form = api.formula(FormulaBuilder::IFF,lhs,rhs);
  AnnotatedFormula af = api.annotatedFormula(form, FormulaBuilder::CONJECTURE);
//  AnnotatedFormula af = api.annotatedFormula(form, FormulaBuilder::AXIOM);

  cout<<af<<endl;

  Problem p1;
  p1.addFormula(af);
  printProblem(p1);

  AnnotatedFormulaIterator fit1=p1.formulas();
  fit1.hasNext();
  cout<<fit1.next().toString()<<endl;


//  string fs=af.toString();
//
//  stringstream sstr(fs);
//
//  Problem p2;
//  p2.addFromStream(sstr);
//  printProblem(p2);

  Problem p3=p1.clausify();
  printProblem(p3);

  AnnotatedFormulaIterator fit2=p3.formulas();
  fit2.hasNext();
  cout<<fit2.next().toString()<<endl;


  return 0;

  AnnotatedFormulaIterator fit=p3.formulas();
  fit.hasNext();
  cout<<"deleting "<<fit.next()<<endl;
  fit.del();

  printProblem(p3);
  return 0;
  ifstream finp("Problems/PUZ/PUZ001+1.p");
  if(!finp.fail()) {
    Problem p4;
    p4.addFromStream(finp);
    printProblem(p4);

    Problem p5=p4.clausify();
    printProblem(p5);
  }

  return 0;
}
