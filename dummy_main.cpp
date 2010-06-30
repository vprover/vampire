/**
 * @file dummy_main.cpp
 * Contains an empty main function (to be linked with api interfaces)
 */

#include <iostream>

#include "Api/FormulaBuilder.hpp"
#include "Api/ResourceLimits.hpp"

using namespace std;
using namespace Api;

int main(int argc, char* argv [])
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


  cout<<result.toString();

  return 0;
}
