/**
 * @file test_vapi.cpp
 * Source of the test executable for the libvapi.
 */

#include <iostream>
#include <fstream>
#include <sstream>
#include <string>

#include "Api/FormulaBuilder.hpp"
#include "Api/Problem.hpp"

#include "Lib/Environment.hpp"
#include "Kernel/Signature.hpp"

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
  LOGV(env.signature->functions());
  for(int i=0;i<env.signature->functions();i++) {
    if(env.signature->functionArity(i)>0) {
      LOGV(i);
      LOGV(env.signature->functionArity(i));
    }
  }
}

int main(int argc, char* argv [])
{

  if(argc==2) {
    clausifyTest(argv[1]);
    return 0;
  }

  FormulaBuilder api(true);
  LOG('a');
  Var xv = api.var("X"); // variable x
  Var yv = api.var("Y"); // variable y
  Term x =  api.varTerm(xv); // term x
  Term y =  api.varTerm(yv); // term y
  Function f = api.function("f",1);
  Term fx = api.term(f,x); // f(X)
  Term fy = api.term(f,y); // f(Y)
  Formula lhs = api.equality(fx,fy); // f(X) = f(Y)
  Predicate p=api.predicate("p",3);
  Formula rhs = api.formula(p,x,fx,fy); // p(X,f(X),f(Y))

  Formula form = api.formula(FormulaBuilder::IFF,lhs,rhs);
//  AnnotatedFormula af = api.annotatedFormula(form, FormulaBuilder::CONJECTURE);
  AnnotatedFormula af = api.annotatedFormula(form, FormulaBuilder::AXIOM);


  LOG('a');
  cout<<af<<endl;
  LOG('a');

  Problem p1;
  p1.addFormula(af);
  printProblem(p1);

//  string fs=af.toString();
//
//  stringstream sstr(fs);
//
//  Problem p2;
//  p2.addFromStream(sstr);
//  printProblem(p2);

  Problem p3=p1.clausify();
  printProblem(p3);

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
