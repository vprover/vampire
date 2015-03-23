#include<iostream>
#include<z3++.h>
using namespace z3;

#include "Test/UnitTesting.hpp"
#include "Lib/Allocator.hpp"

using namespace Lib;

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
*/
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
/*
  cout << s.check() << endl;

  cout << "model" << endl;
  model m = s.get_model();
  for(unsigned i=0; i < m.size(); i++){
    func_decl v = m[i];
    cout << v.name() << " = " << m.get_const_interp(v) << endl;
  }
*/
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

