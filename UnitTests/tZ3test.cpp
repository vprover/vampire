
/*
 * File tZ3test.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
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
  symbol->setType(new FunctionType(Sorts::SRT_INTEGER,Sorts::SRT_INTEGER));

  symbol = env.signature->getPredicate(pow2);
  symbol->setType(new PredicateType(Sorts::SRT_INTEGER));

  Term* sk0_12 = Term::create1(sk0,TermList(twelve));

  Literal* pow2_12 = Literal::create1(pow2,true,TermList(twelve));
  Literal* pow2_1 = Literal::create1(pow2,true,TermList(one));
  Literal* sk0_12_eq_6 = Literal::createEquality(true,TermList(sk0_12),TermList(six),Sorts::SRT_INTEGER);

  SAT::SAT2FO s2f;
  SAT::Z3Interfacing* sat = new SAT::Z3Interfacing(*env.options,s2f);

  expr pow2_12_rep = sat->getz3expr(pow2_12,true);
  expr pow2_1_rep = sat->getz3expr(pow2_1,true);
  expr sk0_12_eq_6_rep = sat->getz3expr(sk0_12_eq_6,true);

}

TEST_FUN(example_model){
  std::cout << "find_model_example1\n"; // see https://github.com/dtrebbien/Z3/blob/master/examples/c++/example.cpp
  context c;
  expr x = c.int_const("x");
  expr y = c.int_const("y");
  solver s(c);

  s.add(x >= 1);
  s.add(y < x + 3);
  std::cout << s.check() << "\n";

  model m = s.get_model();
  std::cout << m << "\n";
  // traversing the model
  for (unsigned i = 0; i < m.size(); i++) {
      func_decl v = m[i];
      // this problem contains only constants
      assert(v.arity() == 0);
      std::cout << v.name() << " = " << m.get_const_interp(v) << "\n";
  }
  // we can evaluate expressions in the model.
  std::cout << "x + y + 1 = " << m.eval(x + y + 1) << "\n";
}
TEST_FUN(models_on_unknown){
  try{
  std::cout << "models_on_unknown\n";
  context c;
  expr x = c.int_const("x");
  expr y = c.int_const("y");
  expr z = c.int_const("z");
  expr a = c.int_const("a");
  solver s(c);

  s.add(a > 1);
  s.add(x > 0);
  s.add(y > 0);
  s.add(z > 0);
  expr statement = ((x*x*x) + (y*y*y)) == (z*z*z);
  s.add(statement);
  std::cout << s.check() << "\n";

  model m = s.get_model();
  std::cout << "have model" << endl;
  std::cout << m << "\n";
  // traversing the model
  for (unsigned i = 0; i < m.size(); i++) {
      func_decl v = m[i];
      // this problem contains only constants
      assert(v.arity() == 0);
      //std::cout << v.name() << " = " << m.get_const_interp(v) << "\n";
      std::cout << v.name() << endl; 
  }
  // we can evaluate expressions in the model.
  //std::cout << "x = " << m.eval(x + y + 1) << "\n";
  }
  catch(z3::exception& exception){
    cout << "Z3 exception:\n" << exception.msg() << endl;
  }
}
*/
TEST_FUN(division){
  std::cout << "z3 division" << endl;

  try{

  unsigned div = theory->getFnNum(Theory::REAL_QUOTIENT);
  TermList zero(theory->representConstant(RealConstantType("0")));
  TermList one(theory->representConstant(RealConstantType("1")));

  unsigned afun = env.signature->addFunction("a",0); 
  Signature::Symbol* symbol = env.signature->getFunction(afun);
  symbol->setType(new FunctionType(Sorts::SRT_REAL));
  unsigned bfun = env.signature->addFunction("b",0);    
  symbol = env.signature->getFunction(bfun);
  symbol->setType(new FunctionType(Sorts::SRT_REAL));
  unsigned cfun = env.signature->addFunction("c",0);    
  symbol = env.signature->getFunction(cfun);
  symbol->setType(new FunctionType(Sorts::SRT_REAL));

  TermList a(Term::createConstant(afun)); 
  TermList b(Term::createConstant(bfun)); 
  TermList c(Term::createConstant(cfun)); 
  TermList divab(Term::create2(div, a, b));
  Literal* lit = Literal::createEquality(true, c, divab, Sorts::SRT_REAL);

  SAT::SAT2FO s2f;
  SAT::Z3Interfacing* sat = new SAT::Z3Interfacing(*env.options,s2f);

  Clause * cl = new(1) Clause(1,Unit::AXIOM,new Inference0(Inference::INPUT));
  (* cl)[0] = lit;
  sat->addClause(s2f.toSAT(cl),true);

  cl = new(1) Clause(1,Unit::AXIOM,new Inference0(Inference::INPUT));
  (* cl)[0] = Literal::createEquality(true,a,one,Sorts::SRT_REAL);
  sat->addClause(s2f.toSAT(cl),true);

  cout << sat->solve(0) << endl;

  }catch(z3::exception& exception){
    cout << "Z3 exception:\n" << exception.msg() << endl;
  }
}


#endif

