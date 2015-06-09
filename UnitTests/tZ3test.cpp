#if VZ3

#include<iostream>
#include<z3++.h>
using namespace z3;

#include "Test/UnitTesting.hpp"
#include "Lib/Allocator.hpp"
#include "Kernel/Term.hpp"
#include "Lib/Environment.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Sorts.hpp"
#include "SAT/SAT2FO.hpp"
#include "SAT/Z3Interfacing.hpp"
#include "Indexing/TermSharing.hpp"

using namespace Lib;
using namespace Kernel;

#define UNIT_ID z3
UT_CREATE;

/*
TEST_FUN(first){
  BYPASSING_ALLOCATOR
  context c;
  expr x = c.int_const("x");
  std::cout << x + 1 << "\n";
}

TEST_FUN(incremental3){ // taken from z3.codeplex.com/SourceControl/latest#examples/c++/examples.cpp
  BYPASSING_ALLOCATOR

  cout << "incremental example" << endl;
  context c;
  expr x = c.int_const("x");
  solver s(c);
  s.add(x > 0);
  cout << s.check() << endl;

  expr b = c.bool_const("b");
  s.add(implies(b, x < 0));
  
  expr_vector a1(c);
  a1.push_back(b);
  cout << s.check(a1) << endl;

  cout << s.check() << endl;

  expr_vector a2(c);
  a2.push_back(!b);
  cout << s.check(a2) << endl;

}
TEST_FUN(our_usage){
  cout << endl;
  BYPASSING_ALLOCATOR;

  context c;
  solver s(c);

  params p(c);
  p.set("unsat_core",true);
  s.set(p);

  // we get clauses (1 or 2) (-1 or 3)
  expr v1 = c.bool_const("v1");
  expr v2 = c.bool_const("v2");
  expr v3 = c.bool_const("v3");

  s.add(v1 || v2,"c1");
  s.add(!v1 || v3,"c2");
  cout << s.check() << endl;

  cout << "model" << endl;
  model m = s.get_model();
  //for(unsigned i=0; i < m.size(); i++){
  //  func_decl v = m[i];
  //  cout << v.name() << " = " << m.get_const_interp(v) << endl;
  //}
  cout << "v1: " << m.eval(v1) << endl;
  cout << "v2: " << m.eval(v2) << endl;
  cout << "v3: " << m.eval(v3) << endl;

  s.add(!v3,"c3");
  s.add(!v2 || v3,"c4");
  cout << s.check() << endl;

  // now unsat, extract core
  expr_vector core = s.unsat_core();
  cout << "core" << endl;
  cout << "size: " << core.size() << endl;

  for(unsigned i=0; i < core.size(); i++){
    cout << core[i] << endl;
  }

}
*/
TEST_FUN(seg_issue){
  cout << endl;
  BYPASSING_ALLOCATOR;

  Term* one = new(0) Term;
  one->makeSymbol(env.signature->addIntegerConstant("1",false),0);
  one = env.sharing->insert(one);
  Term* six = new(0) Term;
  six->makeSymbol(env.signature->addIntegerConstant("6",false),0);
  six = env.sharing->insert(six);
  Term* twelve = new(0) Term;
  twelve->makeSymbol(env.signature->addIntegerConstant("12",false),0);
  twelve = env.sharing->insert(twelve);
  
  unsigned pow2 = env.signature->addPredicate("pow2",1); 
  unsigned sk0 = env.signature->addSkolemFunction(1);

  Signature::Symbol* symbol = env.signature->getFunction(sk0);
  symbol->setType(BaseType::makeType1(Sorts::SRT_INTEGER,Sorts::SRT_INTEGER));

  symbol = env.signature->getPredicate(pow2);
  symbol->setType(BaseType::makeType1(Sorts::SRT_INTEGER,Sorts::SRT_BOOL));

  Term* sk0_12 = Term::create1(sk0,TermList(twelve));

  Literal* pow2_12 = Literal::create1(pow2,true,TermList(twelve));
  Literal* pow2_1 = Literal::create1(pow2,true,TermList(one));
  Literal* sk0_12_eq_6 = Literal::createEquality(true,TermList(sk0_12),TermList(six),Sorts::SRT_INTEGER);

  SAT::SAT2FO s2f;
  SAT::Z3Interfacing* sat = new SAT::Z3Interfacing(*env.options,s2f,false);

  expr pow2_12_rep = sat->getz3expr(pow2_12,true);
  expr pow2_1_rep = sat->getz3expr(pow2_1,true);
  expr sk0_12_eq_6_rep = sat->getz3expr(sk0_12_eq_6,true);

}
#endif

