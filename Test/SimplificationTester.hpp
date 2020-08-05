/**
 * This file provides macros and classes used to write nice tests for simplification rules.
 *
 * Check out UnitTests/tGaussianElimination.cpp, to see how it is to be used.
 */

#include "Test/TestUtils.hpp"
#include "Kernel/Clause.hpp"

namespace Test {

  namespace Simplification {

class SimplificationTester
{
public:
  virtual Kernel::Clause* simplify(Kernel::Clause*) const = 0;

  virtual bool eq(Kernel::Clause const* lhs, Kernel::Clause const* rhs) const 
  {
    return TestUtils::eqModAC(lhs, rhs);
  }
};

struct Success
{
  Kernel::Clause& input;
  Kernel::Clause& expected;

  void run(const SimplificationTester& simpl) {
    auto res = simpl.simplify(&input);

    if (!res) {
      cout  << endl;
      cout << "[     case ]: " << input.toString() << endl;
      cout << "[       is ]: NULL (indicates the clause is a tautology)" << endl;
      cout << "[ expected ]: " << expected.toString() << endl;
      exit(-1);

    } else if (!simpl.eq(res, &expected)) {
      cout  << endl;
      cout << "[     case ]: " << input.toString() << endl;
      cout << "[       is ]: " << res->toString() << endl;
      cout << "[ expected ]: " << expected.toString() << endl;
      exit(-1);

    }
  }
};

struct NotApplicable
{
  Kernel::Clause& input;

  void run(const SimplificationTester& simpl) {
    auto res = simpl.simplify(&input);
    if (res != &input ) {
      cout  << endl;
      cout << "[     case ]: " << input.toString() << endl;
      cout << "[       is ]: " << res->toString() << endl;
      cout << "[ expected ]: < nop >" << endl;
      exit(-1);
    }
  }
};

#define REGISTER_SIMPL_TESTER(t) using SimplTester = t;

#define TEST_SIMPLIFY(name, ...)                                                                                        \
        TEST_SIMPLIFY_WITH_SUGAR(name, SIMPL_SUGAR, __VA_ARGS__) 

#define TEST_SIMPLIFY_WITH_SUGAR(name, syntax_sugar, ...)                                                               \
  TEST_FUN(name) {                                                                                                      \
    SimplTester simpl;                                                                                                  \
    _Pragma("GCC diagnostic push")                                                                                      \
    _Pragma("GCC diagnostic ignored \"-Wunused\"")                                                                      \
      syntax_sugar                                                                                                      \
    _Pragma("GCC diagnostic pop")                                                                                       \
    __VA_ARGS__.run(simpl);                                                                                             \
  }                                                                                                                     \

} // namespace Simplification

} // namespace Test
