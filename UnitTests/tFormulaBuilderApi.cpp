
#include <iostream>
#include <sstream>
#include <map>

#include "Api/FormulaBuilder.hpp"
#include "Api/Problem.hpp"

#include "Lib/DHSet.hpp"

#include "Kernel/Term.hpp"

#include "Test/UnitTesting.hpp"

#define UNIT_ID fbapi
UT_CREATE;

using namespace std;
using namespace Api;



TEST_FUN(fbapi1)
{
  try {
    FormulaBuilder api(true);

    Var xv = api.var("X"); // variable x
    Var yv = api.var("Y"); // variable y
    Term x =  api.varTerm(xv); // term x
    Term y =  api.varTerm(yv); // term y
    Function f = api.function("f",1);
    Term fx = api.term(f,x); // f(x)
    Term fy = api.term(f,y); // f(y)
    Formula lhs = api.equality(fx,fy); // f(x) = f(y)
    Predicate p=api.predicate("p",3);
    Formula rhs = api.formula(p,x,fx,fy); // p(X0,f(X0),f(X1))

    Formula result = api.formula(FormulaBuilder::IMP,lhs,rhs); // f(X0) = f(X1) => p(X0,f(X0),f(X1))


    string formString=result.toString();

    stringstream sstr;
    sstr << result;
    ASS_EQ(sstr.str(), formString);

    cout << endl << "Should print something like \"f(X) = f(Y) => p(X,f(X),f(Y))\"" << endl;
    // example: output
    cout << formString << endl;

    AnnotatedFormula ares = api.annotatedFormula(result, FormulaBuilder::ASSUMPTION);
    cout << endl << "Should print something like \"fof(u1,hypothesis,( f(X) = f(Y) => p(X,f(X),f(Y)) )).\"" << endl;
    cout << ares << endl;

    AnnotatedFormula ares2 = api.annotatedFormula(result, FormulaBuilder::CONJECTURE, "conj123");
    cout << endl << "Should print something equivalent to \"fof(conj123,conjecture,( f(X) = f(Y) => p(X,f(X),f(Y)) )).\"" << endl;
    cout << ares2 << endl;
  }
  catch (FormulaBuilderException e)
  {
    cout<< "Exception: "<<e.msg()<<endl;
    throw;
  }
}

TEST_FUN(fbapiReflection)
{
  try {
    FormulaBuilder api(true);

    Var xv = api.var("X"); // variable x
    Var yv = api.var("Y"); // variable y
    Term x =  api.varTerm(xv); // term x
    Term y =  api.varTerm(yv); // term y
    Function fun = api.function("f",1);
    Term fx = api.term(fun,x); // f(x)
    Term fy = api.term(fun,y); // f(y)
    Formula f1 = api.equality(fx,fy); // f(x) = f(y)

    Formula f1neg = api.negation(f1);

    ASS(f1neg.isNegation());
    ASS(!f1neg.boundVars().hasNext());


    DHSet<string> vs;
    vs.loadFromIterator(f1neg.freeVars());
    ASS_EQ(vs.size(),2);
    ASS(vs.find("X"));
    ASS(vs.find("Y"));

    AnnotatedFormula af1neg = api.annotatedFormula(f1neg, FormulaBuilder::ASSUMPTION);
    ASS(!af1neg.boundVars().hasNext());

    vs.reset();
    vs.loadFromIterator(af1neg.freeVars());
    ASS_EQ(vs.size(),2);
    ASS(vs.find("X"));
    ASS(vs.find("Y"));

    AnnotatedFormula af1conj = api.annotatedFormula(f1neg, FormulaBuilder::CONJECTURE);
    ASS(!af1conj.freeVars().hasNext());

    vs.reset();
    vs.loadFromIterator(af1conj.boundVars());
    ASS_EQ(vs.size(),2);
    ASS(vs.find("X"));
    ASS(vs.find("Y"));


    ASS(api.trueFormula().isTrue());
    ASS(api.falseFormula().isFalse());

    Formula fnull;
    ASS(fnull.isNull());
    ASS(!fnull.freeVars().hasNext());

    Term tnull;
    ASS(tnull.isNull());

    AnnotatedFormula afnull;
    ASS(afnull.isNull());

    cout<<endl<<af1neg.toString()<<endl;
    cout<<af1neg.formula().toString()<<endl;
    cout<<af1conj.toString()<<endl;
    cout<<af1conj.formula().toString()<<endl;
    ASS_EQ(af1neg.annotation(),FormulaBuilder::ASSUMPTION);
    ASS_EQ(af1conj.annotation(),FormulaBuilder::CONJECTURE);
    ASS_EQ(af1neg.formula().connective(),FormulaBuilder::NOT);
    ASS_EQ(af1conj.formula().connective(),FormulaBuilder::FORALL);
    ASS_EQ(af1conj.formula().formulaArg(0).connective(),FormulaBuilder::NOT);
    ASS_EQ(af1conj.formula().formulaArg(0).formulaArg(0).connective(),FormulaBuilder::ATOM);
    ASS_EQ(af1conj.formula().formulaArg(0).formulaArg(0).predicate(),0);
    ASS_EQ(af1conj.formula().formulaArg(0).formulaArg(0).argCnt(),2);
    Term t = af1conj.formula().formulaArg(0).formulaArg(0).termArg(1);
    ASS(!t.isVar());
    ASS_EQ(t.functor(),fun);
    ASS_EQ(t.arity(),1);
    ASS(t.arg(0).isVar());
    ASS_NEQ(af1conj.formula().formulaArg(0).formulaArg(0).termArg(0).arg(0).var(), t.arg(0).var());
  }
  catch (FormulaBuilderException e)
  {
    cout<< "Exception: "<<e.msg()<<endl;
    throw;
  }
}

TEST_FUN(fbapiSubst)
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

TEST_FUN(fbapiStrConv)
{
  try {
    FormulaBuilder api(true, true);

    Function xv = api.var("X");
    Function yv = api.var("Y");
    Function ct = api.function("c",0);
    Function f = api.function("f",1);
    Function g = api.function("g",2);
    Predicate p = api.predicate("p",1);

    Term x = api.varTerm(xv); // c
    Term y = api.varTerm(yv); // c
    Term c = api.term(ct); // c
    Term fc = api.term(f,c); // f(c)
    Term ffc = api.term(f,fc); // f(c)
    Term fffc = api.term(f,ffc); // f(c)

    Term gxfffc = api.term(g,x,fffc); // g(X,f(f(f(c))))
    ASS_EQ(gxfffc.toString(), "g(X,f(f(f(c))))");

    Term fgxfffc = api.term(f,gxfffc); // f(g(X,f(f(f(c)))))

    Term gfgxfffcfgxfffc = api.term(g,fgxfffc,fgxfffc); // g(f(g(X,f(f(f(c))))),f(g(X,f(f(f(c))))))
    ASS_EQ(gfgxfffcfgxfffc.toString(), "g(f(g(X,f(f(f(c))))),f(g(X,f(f(f(c))))))");

    Formula f1=api.equality(gxfffc,y);
    ASS_NEQ(f1.toString().find("Y"), string::npos);
    ASS_NEQ(f1.toString().find("g(X,f(f(f(c))))"), string::npos);
    ASS_NEQ(f1.toString().find("="), string::npos);

    Formula f2=api.atom(p,&gfgxfffcfgxfffc, false);
    ASS_EQ(f2.toString(), "~p(g(f(g(X,f(f(f(c))))),f(g(X,f(f(f(c)))))))");

    Formula f3=api.formula(FormulaBuilder::AND, api.negation(f1), api.formula(FormulaBuilder::EXISTS,xv,f2));
    ASS_REP2(f3.toString().find(f1.toString())!=string::npos, f3.toString(),f1.toString());
    ASS_REP2(f3.toString().find(f2.toString())!=string::npos, f3.toString(),f2.toString());
    ASS_REP(f3.toString().find("[X]")!=string::npos, f3.toString());

    try{
      Formula f4=api.formula(FormulaBuilder::EXISTS,xv,f3); //binding bound variable
      ASSERTION_VIOLATION;
    } catch(FormulaBuilderException) {
    }
  }
  catch (FormulaBuilderException e)
  {
    cout<< "Exception: "<<e.msg()<<endl;
    throw;
  }


}

TEST_FUN(fbapiErrors)
{
  FormulaBuilder api(true, true);

  try {
    api.var("x"); // lowercase variable name
    ASSERTION_VIOLATION;
  } catch (InvalidTPTPNameException e)
  {
    ASS_EQ(e.name(), "x");
  }

  try {
    api.function("F",1); // uppercase function name
    ASSERTION_VIOLATION;
  } catch (InvalidTPTPNameException e)
  {
    ASS_EQ(e.name(), "F");
  }

  try {
    api.predicate("P",1); // uppercase predicate name
    ASSERTION_VIOLATION;
  } catch (InvalidTPTPNameException e)
  {
    ASS_EQ(e.name(), "P");
  }

  Var x = api.var("X");
  Term xt = api.varTerm(x);
  Predicate f = api.function("e_f",4);
  Predicate p = api.predicate("e_p",4);
  Predicate q = api.predicate("e_q",1);

  try {
    api.term(f,xt,xt,xt); // invalid function arity
    ASSERTION_VIOLATION;
  } catch (FormulaBuilderException e)
  {
  }

  try {
    api.formula(p,xt,xt,xt); // invalid predicate arity
    ASSERTION_VIOLATION;
  } catch (FormulaBuilderException e)
  {
  }

  try{
    FormulaBuilder api2(true);
    Formula f2=api2.negation(api.formula(q,xt)); //mixing formulas from diferent FormulaBuilders
    ASSERTION_VIOLATION;
  }
  catch (FormulaBuilderException e)
  {
  }

  try{
    Formula f1=api.formula(FormulaBuilder::FORALL,x,api.formula(q,xt));
    Formula f2=api.formula(FormulaBuilder::FORALL,x,f1); //binding bound variable
    ASSERTION_VIOLATION;
  }
  catch (FormulaBuilderException e)
  {
  }
}

TEST_FUN(fbapiProblem)
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

TEST_FUN(fbapiClausify)
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

TEST_FUN(fbapiClausifyDefinitions)
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

TEST_FUN(fbapiPDInlining)
{
  try {
    FormulaBuilder api;

    Var xv = api.var("Var");
    Var yv = api.var("Var2");
    Predicate cSym=api.function("c",0);
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
  } catch (ApiException e) {
    cout<<"Exception: "<<e.msg()<<endl;
    throw;
  }
}

TEST_FUN(fbapiPDInlining2)
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

TEST_FUN(fbapiEPRRestoringInlining)
{
  try {
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
  } catch (ApiException e) {
    cout<<"Exception: "<<e.msg()<<endl;
    throw;
  }
}

TEST_FUN(fbapiAsymReplacement)
{
  try {
    Problem prb;
    stringstream stm(
	"fof(a1,axiom, p(X) <=> r). fof(a2,hypothesis, p(X) => (q|s)). fof(a3,axiom, ~r => p(X)). fof(a4,axiom, p(X)).");
    prb.addFromStream(stm);

    cout<<endl<<"FOF:"<<endl;
    AnnotatedFormulaIterator afit=prb.formulas();
    while(afit.hasNext()) {
      cout<<afit.next()<<endl;
    }

    FormulaBuilder api;

    Var xv = api.var("Var");
    Predicate cSym=api.function("c",0);
    Predicate dSym=api.function("d",0);
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
    afit=iprb.formulas();
    while(afit.hasNext()) {
      cout<<afit.next()<<endl;
    }

    iprb=prb.performAsymetricRewriting(fpx, fpc, fqxx, fqcx);
    cout<<"Inlined (px, pc, qxx, qcx):"<<endl;
    afit=iprb.formulas();
    while(afit.hasNext()) {
      cout<<afit.next()<<endl;
    }

    Formula lhsA[] = {fpx,api.negation(fr)};
    Formula rhsPosA[] = {fOr,fqdd};
    Formula rhsNegA[] = {ft,fqdd};
    Formula rhsDblA[] = {fqxx,fqdd};
    iprb=prb.performAsymetricRewriting(2, lhsA, rhsPosA, rhsNegA, rhsDblA);
    cout<<"Inlined arr:"<<endl;
    afit=iprb.formulas();
    while(afit.hasNext()) {
      cout<<afit.next()<<endl;
    }


  } catch (ApiException e) {
    cout<<"Exception: "<<e.msg()<<endl;
    throw;
  }
}


TEST_FUN(fbapiUPDR)
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

string getId(Term t)
{
  static std::map<string,string> idMap;

  stringstream newIdStr;
  newIdStr<<"t_"<<idMap.size();
  string newId=newIdStr.str();

  string id=(*idMap.insert(make_pair(t.toString(), newId)).first).second;
  return id;
}

TEST_FUN(fbapiIds)
{
  FormulaBuilder api;

  Var xv = api.var("X");
  Term x = api.varTerm(xv);
  Predicate f = api.function("f",1);
  Term t=x;
  for(int i=0;i<5;i++) {
    cout<<t.toString()<<" "<<getId(t)<<endl;
    t=api.term(f,t);
  }
  t=x;
  for(int i=0;i<5;i++) {
    cout<<t.toString()<<" "<<getId(t)<<endl;
    t=api.term(f,t);
  }
}

TEST_FUN(fbapiSorts)
{
  try {
    FormulaBuilder api;

    Sort s1 = api.sort("sort1");
    Sort s2 = api.sort("sort2");
    Var xv = api.var("VarS1", s1);
    Var yv = api.var("VarS2", s2);
    Var zv = api.var("VarDef");
    Predicate cSym=api.function("c_s1",0,s1,0);
    Predicate dSym=api.function("d_s2",0,s2,0);
    Term x = api.varTerm(xv);
    Term y = api.varTerm(yv);
    Term z = api.varTerm(zv);
    Term c = api.term(cSym);
    Term d = api.term(dSym);

    ASS_EQ(x.sort(), s1);
    ASS_EQ(y.sort(), s2);
    ASS_EQ(z.sort(), api.defaultSort());
    ASS_EQ(c.sort(), s1);
    ASS_EQ(d.sort(), s2);

    Predicate p=api.predicate("p_s1",1,&s1);
    Predicate r=api.predicate("r_s2",1,&s2);
    Sort qSorts[] = {s1, s2, api.defaultSort()};
    Predicate q=api.predicate("q_s1_s2_i",3,qSorts);

    Formula fpx=api.formula(p,x);
    Formula fpc=api.formula(p,c);
    Formula fry=api.formula(r,y);
    Formula frd=api.formula(r,d);
    Formula fqxyz=api.formula(q,x,y,z);
    Formula fqcdz=api.formula(q,c,d,z);
    Formula fxEQx=api.equality(x,x);
    Formula fxEQc=api.equality(x,c);
    Formula fxEQc2=api.equality(x,c,s1);
    Formula fzEQz=api.equality(z,z);
    Formula fOr=api.formula(FormulaBuilder::OR, fqxyz, frd);
    Formula fEx=api.formula(FormulaBuilder::EXISTS, xv, fOr);
    AnnotatedFormula af = api.annotatedFormula(fEx, FormulaBuilder::AXIOM, "ax1");

    Formula fAnd=api.formula(FormulaBuilder::AND, fpx, fry);
    Formula fOr2=api.formula(FormulaBuilder::OR, fAnd, fAnd);
    Formula fOr4=api.formula(FormulaBuilder::OR, fOr2, fOr2);
    Formula fOr8=api.formula(FormulaBuilder::OR, fOr4, fOr4);
    AnnotatedFormula af2 = api.annotatedFormula(fOr8, FormulaBuilder::AXIOM, "ax2");

    OutputOptions::setSortedEquality(true);
    cout<<fxEQc<<" ";
    OutputOptions::setSortedEquality(false);
    cout<<fxEQc<<endl;

    OutputOptions::setSortedEquality(true);
    cout<<fxEQx<<" ";
    OutputOptions::setSortedEquality(false);
    cout<<fxEQx<<endl;

    OutputOptions::setSortedEquality(true);
    cout<<fzEQz<<" ";
    OutputOptions::setSortedEquality(false);
    cout<<fzEQz<<endl;

    Problem prb;
    prb.addFormula(af);
    prb.addFormula(af2);
    cout<<"Orig:"<<endl<<af<<af2<<endl;
    prb.outputTypeDefinitions(cout);

    cout<<"Clausified:"<<endl;
    Problem cprb = prb.clausify(4,true,Problem::INL_OFF,false);
    AnnotatedFormulaIterator afit=cprb.formulas();
    while(afit.hasNext()) {
      cout<<afit.next()<<endl;
    }
    prb.outputTypeDefinitions(cout, true);

    try{
      api.equality(x,y);
      ASSERTION_VIOLATION;
    } catch (SortMismatchException e)
    {}

    try{
      api.equality(x,c, s2);
      ASSERTION_VIOLATION;
    } catch (SortMismatchException e)
    {}

    try{
      api.formula(q,x,y,c);
      ASSERTION_VIOLATION;
    } catch (SortMismatchException e)
    {}

    try{
      api.predicate("p1234",1,&s1);
      api.predicate("p1234",1,&s2);
      ASSERTION_VIOLATION;
    } catch (FormulaBuilderException e)
    {}

    try{
      api.var("Var1234",s1);
      api.var("Var1234",s2);
      ASSERTION_VIOLATION;
    } catch (FormulaBuilderException e)
    {}

  } catch (ApiException e) {
    cout<<"Exception: "<<e.msg()<<endl;
    throw;
  }
}

TEST_FUN(fbapiSine)
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
    Problem prb2 = prb.preprocess(opts);
    prb2.output(cout, false);

  } catch (ApiException e) {
    cout<<"Exception: "<<e.msg()<<endl;
    throw;
  }
}



