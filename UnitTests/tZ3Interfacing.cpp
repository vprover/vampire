
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

/** runs z3 on a bunch of vampire literals as assuptions, and checks the status afterwards */
void checkStatus(SATSolver::Status expected, Stack<Literal*> assumptions) 
{

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
/////////////////////////////////////////////////////////////////////////////////////////
// Simple tests
/////////////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////
// Rational Tests
/////////////////

TEST_FUN(rat__simple_01) {
  NUMBER_SUGAR(Rat)
  checkStatus(
      SATSolver::UNSATISFIABLE, 
      { num(3) == num(0) });
}

TEST_FUN(rat__simple_02) {
  NUMBER_SUGAR(Rat)
  DECL_CONST(a, Rat)
  checkStatus(
      SATSolver::SATISFIABLE, 
      { num(3) == a });
}


TEST_FUN(rat__simple_03) {
  NUMBER_SUGAR(Rat)
  checkStatus(
      SATSolver::UNSATISFIABLE, 
      { num(3) == num(3) + 2 * num(7) });
}

TEST_FUN(rat__simple_04) {
  NUMBER_SUGAR(Rat)
  checkStatus(
      SATSolver::UNSATISFIABLE, 
      { num(17) != num(3) + 2 * num(7) });
}

////////////////////////////////////
// FOOL Tests
/////////////////

TEST_FUN(fool__simple_01) {
  DECL_VAR(x, 0);
  checkStatus(
      SATSolver::SATISFIABLE, 
      { fool(false) == x });
}

TEST_FUN(fool__simple_02) {
  DECL_VAR(x, 0);
  checkStatus(
      SATSolver::SATISFIABLE, 
      { fool(true) == x });
}


TEST_FUN(fool__simple_03) {
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



TEST_FUN(dty__01) {
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


TEST_FUN(dty__02) {
  DECL_EVEN_ODD
  checkStatus(SATSolver::UNSATISFIABLE, { succEven(succOdd(zero)) == zero });
}


TEST_FUN(dty__03_01) {
  // we have a non-mutually recursive datatype that depends on a non-mutual but recursive datatype that 
  DECL_EVEN_ODD
  DECL_LIST(even)
  // request non-mutual first
  checkStatus(SATSolver::UNSATISFIABLE, { cons(succEven(succOdd(zero)), nil) == cons(zero, nil) });
}

TEST_FUN(dty__03_02) {
  // we have a non-mutually recursive datatype that depends on a non-mutual but recursive datatype that 
  DECL_EVEN_ODD
  DECL_LIST(even)
  // request mutual only
  checkStatus(SATSolver::UNSATISFIABLE, { succEven(succOdd(zero)) == zero });
}

TEST_FUN(dty__03_03) {
  // we have a non-mutually recursive datatype that depends on a non-mutual but recursive datatype that 
  DECL_EVEN_ODD
  DECL_LIST(even)
  // request mutual first
  checkStatus(SATSolver::UNSATISFIABLE, { succEven(succOdd(zero)) == zero });
  checkStatus(SATSolver::UNSATISFIABLE, { cons(succEven(succOdd(zero)), nil) == cons(zero, nil) });
}


/**
   \brief Create the binary function application: <tt>(f x y)</tt>.
*/
Z3_ast Z3_mk_binary_app(Z3_context ctx, Z3_func_decl f, Z3_ast x, Z3_ast y)
{
    Z3_ast args[2] = {x, y};
    return Z3_mk_app(ctx, f, 2, args);
}

/**
   \brief Create a variable using the given name and type.
*/
Z3_ast Z3_mk_var(Z3_context ctx, const char * name, Z3_sort ty)
{
    Z3_symbol   s  = Z3_mk_string_symbol(ctx, name);
    return Z3_mk_const(ctx, s, ty);
}
/**
   \brief exit gracefully in case of error.
*/
void exitf(const char* message)
{
  fprintf(stderr,"BUG: %s.\n", message);
  exit(1);
}

/**
   \brief Simpler error handler.
 */
void error_handler(Z3_context c, Z3_error_code e)
{
    printf("Error code: %d\n", e);
    exitf("incorrect use of Z3");
}

/**
   \brief Create a logical context.

   Enable model construction. Other configuration parameters can be passed in the cfg variable.

   Also enable tracing to stderr and register custom error handler.
*/
Z3_context mk_context_custom(Z3_config cfg, Z3_error_handler err)
{
    Z3_context ctx;

    Z3_set_param_value(cfg, "model", "true");
    ctx = Z3_mk_context(cfg);
    Z3_set_error_handler(ctx, err);

    return ctx;
}



#endif // VZ3
