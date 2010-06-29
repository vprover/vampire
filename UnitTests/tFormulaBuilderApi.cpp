
#include <iostream>
#include <sstream>

#include "Api/FormulaBuilder.hpp"

#include "Test/UnitTesting.hpp"

#define UNIT_ID fbapi
UT_CREATE;

using namespace std;
using namespace Api;



TEST_FUN(fbapi1)
{
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

  AnnotatedFormula ares2 = api.annotatedFormula(result, FormulaBuilder::CONJECTURE);
  cout << endl << "Should print something equivalent to \"fof(u1,conjecture,( f(X0) = f(X1) => p(X0,f(X0),f(X1)) )).\"" << endl;
  cout << ares2 << endl;

}

TEST_FUN(fbapiErrors)
{
  FormulaBuilder api(true);

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
}
