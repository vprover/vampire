
#include <iostream>
#include <sstream>
#include <map>

#include "Api/FormulaBuilder.hpp"
#include "Api/Problem.hpp"

#include "Lib/DHSet.hpp"

#include "Kernel/Term.hpp"

#include "Test/UnitTesting.hpp"

#define UNIT_ID ite
UT_CREATE;

using namespace std;
using namespace Api;



TEST_FUN(ite1)
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
    Predicate p=api.predicate("p",3);
    Formula pXfXfY = api.formula(p,x,fx,fy); // p(X,f(X),f(Y))

//    Predicate q1=api.predicate("q1",0);
    Predicate q2=api.predicate("q2",0);
    Predicate q3=api.predicate("q3",0);
    Formula f1 = api.formula(FormulaBuilder::ITE,pXfXfY,api.formula(q2),api.formula(q3));
    Formula f2 = api.formula(FormulaBuilder::ITE,f1,api.formula(q2),api.formula(q3));
    AnnotatedFormula af1 = api.annotatedFormula(f2, FormulaBuilder::ASSUMPTION);

    cout << endl << "Should print something like \"fof(u1,hypothesis,( f(X) = f(Y) => p(X,f(X),f(Y)) )).\"" << endl;
    cout << af1 << endl;

    Problem p1;
    p1.addFormula(af1);
    Problem p2=p1.clausify();

    AnnotatedFormulaIterator fit1=p2.formulas();
    while(fit1.hasNext()) {
      cout<<fit1.next()<<endl;
    }
  }
  catch (FormulaBuilderException e)
  {
    cout<< "Exception: "<<e.msg()<<endl;
  }
}

