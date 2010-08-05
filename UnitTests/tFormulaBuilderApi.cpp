
#include <iostream>
#include <sstream>

#include "Api/FormulaBuilder.hpp"
#include "Api/Problem.hpp"

#include "Lib/DHSet.hpp"

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

    cout << endl << "Should print something like \"f(X0) = f(X1) => p(X0,f(X0),f(X1))\"" << endl;
    // example: output
    cout << formString << endl;

    AnnotatedFormula ares = api.annotatedFormula(result, FormulaBuilder::ASSUMPTION);
    cout << endl << "Should print something like \"fof(u1,hypothesis,( f(X0) = f(X1) => p(X0,f(X0),f(X1)) )).\"" << endl;
    cout << ares << endl;

    AnnotatedFormula ares2 = api.annotatedFormula(result, FormulaBuilder::CONJECTURE, "conj123");
    cout << endl << "Should print something equivalent to \"fof(conj123,conjecture,( f(X0) = f(X1) => p(X0,f(X0),f(X1)) )).\"" << endl;
    cout << ares2 << endl;
  }
  catch (FormulaBuilderException e)
  {
    cout<< "Exception: "<<e.msg()<<endl;
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
  }
  catch (FormulaBuilderException e)
  {
    cout<< "Exception: "<<e.msg()<<endl;
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






