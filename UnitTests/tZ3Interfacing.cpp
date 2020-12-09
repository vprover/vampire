
  /*
   * File tZ3Interfacing.cpp.
   *
   * This file is part of the source code of the software program
   * Vampire. It is protected by applicable
   * copyright laws.
   *
   * This source code is distributed under the licence found here
   * https://vprover.github.io/license.html
   * and in the source directory
   */
  
#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Kernel/Sorts.hpp"
#include "Test/SyntaxSugar.hpp"
#include "SAT/Z3Interfacing.hpp"

#if VZ3

#define DBG_ON 1
// #if DBG_ON
// #define DEBUG(...)
// #else
// #define DEBUG(...) DBG(__VA_ARGS__)
// #endif

using namespace Shell;
using namespace SAT;

using Sort = unsigned;
using FuncId = unsigned;

/////////////////////////////////////////////////////////////////////////////////////////
// 1) TEST SOLVING
/////////////////////////////////////////////////////////////////////////////////////////

/** runs z3 on a bunch of vampire literals as assuptions, and checks the status afterwards */
void checkStatus(SATSolver::Status expected, Stack<Literal*> assumptions) 
{
  CALL("checkStatus(..)")
  SAT2FO s2f;
  SAT::Z3Interfacing z3(s2f, DBG_ON == 1, false, false);

  for (auto a : assumptions) {
    z3.addAssumption(s2f.toSAT(a));
  }

  auto status = z3.solve();
  if(status != expected) {
    cout << "[ input    ] " << endl;
    for (auto a : assumptions) {
      cout << "\t" << *a << endl;
    }
    cout << "[ expected ] " <<  expected << endl;
    cout << "[ is       ] " <<  status << endl;
    if (status == Z3Interfacing::SATISFIABLE) {
      cout << "[ model    ] " <<  z3.getModel() << endl;

    }
    exit(-1);
  }
}


////////////////////////////////////
// Real Tests
/////////////////

TEST_FUN(solve__real__simple_01) {
  NUMBER_SUGAR(Real)
  checkStatus(
      SATSolver::UNSATISFIABLE, 
      { num(3) == num(0) });
}

TEST_FUN(solve__real__simple_02) {
  NUMBER_SUGAR(Real)
  DECL_CONST(a, Real)
  checkStatus(
      SATSolver::SATISFIABLE, 
      { num(3) == a });
}


TEST_FUN(solve__rat__simple_03) {
  NUMBER_SUGAR(Real)
  checkStatus(
      SATSolver::UNSATISFIABLE, 
      { num(3) == num(3) + 2 * num(7) });
}

TEST_FUN(solve__rat__simple_04) {
  NUMBER_SUGAR(Real)
  checkStatus(
      SATSolver::UNSATISFIABLE, 
      { num(17) != num(3) + 2 * num(7) });
}

////////////////////////////////////
// FOOL Tests
/////////////////

TEST_FUN(solve__fool__simple_01) {
  DECL_VAR(x, 0);
  checkStatus(
      SATSolver::SATISFIABLE, 
      { fool(false) == x });
}

TEST_FUN(solve__fool__simple_02) {
  DECL_VAR(x, 0);
  checkStatus(
      SATSolver::SATISFIABLE, 
      { fool(true) == x });
}


TEST_FUN(solve__fool__simple_03) {
  checkStatus(
      SATSolver::UNSATISFIABLE, 
      { fool(true) == fool(false) });
}

////////////////////////////////////
// term algebra tests
/////////////////

#define DECL_LIST(sort)                                                                                       \
  DECL_SORT(list)                                                                                             \
                                                                                                              \
  DECL_CONST(nil, list)                                                                                       \
  DECL_FUNC(cons, { sort, list  }, list)                                                                      \
                                                                                                              \
  DECL_TERM_ALGEBRA(list, {nil, cons})                                                                        \
  __ALLOW_UNUSED(                                                                                             \
    auto head = cons.dtor(0);                                                                                 \
    auto tail = cons.dtor(1);                                                                                 \
  )                                                                                                           \



TEST_FUN(solve__dty__01) {
  DECL_SORT(alpha)
  DECL_LIST(alpha)

  DECL_CONST(a0, alpha)
  DECL_CONST(a1, alpha)

  checkStatus(SATSolver::UNSATISFIABLE, { cons(a0, nil) == nil });
  checkStatus(SATSolver::UNSATISFIABLE, { cons(a0, nil) == cons(a1, nil), a0 != a1 });
}


// data Even = Zero | SuccEven Odd
// data Odd = SuccOdd Even
#define DECL_EVEN_ODD                                                                                         \
  DECL_SORT(even)                                                                                             \
  DECL_SORT(odd)                                                                                              \
                                                                                                              \
  DECL_CONST(zero, even)                                                                                      \
  DECL_FUNC(succEven, { odd  }, even)                                                                         \
                                                                                                              \
  DECL_FUNC(succOdd, { even }, odd)                                                                           \
                                                                                                              \
  DECL_TERM_ALGEBRA(even, {zero, succEven})                                                                   \
  DECL_TERM_ALGEBRA(odd , {      succOdd })                                                                   \


TEST_FUN(solve__dty__02) {
  DECL_EVEN_ODD
  checkStatus(SATSolver::UNSATISFIABLE, { succEven(succOdd(zero)) == zero });
}


TEST_FUN(solve__dty__03_01) {
  // we have a non-mutually recursive datatype that depends on a non-mutual but recursive datatype that 
  DECL_EVEN_ODD
  DECL_LIST(even)
  // request non-mutual first
  checkStatus(SATSolver::UNSATISFIABLE, { cons(succEven(succOdd(zero)), nil) == cons(zero, nil) });
}

TEST_FUN(solve__dty__03_02) {
  // we have a non-mutually recursive datatype that depends on a non-mutual but recursive datatype that 
  DECL_EVEN_ODD
  DECL_LIST(even)
  // request mutual only
  checkStatus(SATSolver::UNSATISFIABLE, { succEven(succOdd(zero)) == zero });
}

TEST_FUN(solve__dty__03_03) {
  // we have a non-mutually recursive datatype that depends on a non-mutual but recursive datatype that 
  DECL_EVEN_ODD
  DECL_LIST(even)
  // request mutual first
  checkStatus(SATSolver::UNSATISFIABLE, { succEven(succOdd(zero)) == zero });
  checkStatus(SATSolver::UNSATISFIABLE, { cons(succEven(succOdd(zero)), nil) == cons(zero, nil) });
}

/////////////////////////////////////////////////////////////////////////////////////////
// 2) TEST INSTANTIATION
/////////////////////////////////////////////////////////////////////////////////////////

/** 
 * Runs z3 on a bunch of vampire literals as assuptions, that need to be satisfyable. 
 * Then  the term toInstantiate will be instantiated with the model. The instantiated 
 * term will be checked to be equal to the term expected.
 */
void checkInstantiation(Stack<Literal*> assumptions, TermList toInstantiate, TermList expected, bool withGuard = false) 
{
  CALL("checkInstantiation(..)")
  SAT2FO s2f;
  SAT::Z3Interfacing z3(s2f, DBG_ON == 1, false, false);

  for (auto a : assumptions) {
    z3.addAssumption(s2f.toSAT(a), withGuard);
  }

  auto status = z3.solve();
  ASS_EQ(status, Z3Interfacing::SATISFIABLE);
  auto result = z3.evaluateInModel(toInstantiate.term());
  if (result != expected.term()) {
    cout << "[ input    ] " << endl;
    for (auto a : assumptions) {
      cout << "\t" << *a << endl;
    }
    cout << "[ toInstantiate ] " <<  toInstantiate << endl;
    cout << "[ expected      ] " <<  expected << endl;
    cout << "[ is            ] " <<  ( result == nullptr ? "null" : result->toString() ) << endl;
    cout << "[ model         ] " <<  z3.getModel() << endl;
    exit(-1);
  }
}
void checkInstantiationWithGuards(Stack<Literal*> assumptions, TermList toInstantiate, TermList expected)
{ checkInstantiation(std::move(assumptions), toInstantiate, expected, true); }


////////////////////////////////////
// Real Tests
/////////////////

TEST_FUN(instantiate__rat__simple_01) {
  NUMBER_SUGAR(Real)
  DECL_CONST(c, Real)
  checkInstantiation(
      { c * 3 == 9 },
      c, num(3)
      );
}

TEST_FUN(instantiate__rat__simple_02) {
  NUMBER_SUGAR(Real)
  DECL_CONST(c, Real)
  checkInstantiation(
      { c * c == 9, c < 0 },
      c, num(-3)
      );
}

////////////////////////////////////
// term algebra tests
/////////////////


TEST_FUN(instantiate__list_01) {
  NUMBER_SUGAR(Real)
  DECL_LIST(Real)

  DECL_CONST(c, Real)

  checkInstantiation(
      { cons(c, nil) == cons(num(3), nil) },
      c, num(3)
      );
}

TEST_FUN(instantiate__list_02) {
  NUMBER_SUGAR(Real)
  DECL_LIST(Real)

  DECL_CONST(l, list)
  DECL_CONST(h, Real)
  DECL_CONST(t, list)

  checkInstantiation(
      { tail(l) == cons(num(2), nil)
      , head(l) == 1
      , cons(h,t) == l  // <- necessary since selectors are partial
      },
      l, cons(1,cons(2,nil))
      );
}

TEST_FUN(instantiate__list_03) {
  NUMBER_SUGAR(Real)
  DECL_LIST(Real)

  DECL_CONST(l, list)

  checkInstantiationWithGuards(
      { tail(l) == cons(num(2), nil)
      , head(l) == 1
      },
      l, cons(1,cons(2,nil))
      );
}

#endif // VZ3
