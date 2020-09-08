/**
 * This file provides macros and classes used to write nice tests for simplification rules.
 *
 * Check out UnitTests/tGaussianElimination.cpp, to see how it is to be used.
 */

#include "Test/TestUtils.hpp"
#include "Kernel/Clause.hpp"
#include "Lib/Coproduct.hpp"

namespace Test {

  namespace Simplification {

class SimplificationTester
{
public:
  virtual Kernel::Clause* simplify(Kernel::Clause*) const = 0;

  virtual bool eq(Kernel::Clause const* lhs, Kernel::Clause const* rhs) const 
  { return TestUtils::eqModAC(lhs, rhs); }
};

class SimplificationResult;

struct SimplificationAlternative 
{
  unique_ptr<SimplificationResult> lhs;
  unique_ptr<SimplificationResult> rhs;
};

class SimplificationResult : Coproduct<Kernel::Clause const*, SimplificationAlternative>
{
public:
  SimplificationResult(Kernel::Clause const& clause) : Coproduct<Kernel::Clause const*, SimplificationAlternative>(&clause) {}
  SimplificationResult(SimplificationResult l, SimplificationResult r) : Coproduct<Kernel::Clause const*, SimplificationAlternative>(SimplificationAlternative {
        Lib::make_unique<SimplificationResult>(std::move(l)),
        Lib::make_unique<SimplificationResult>(std::move(r))
      }) {}
  bool matches(const SimplificationTester& simpl, Kernel::Clause const& result);
  friend ostream& operator<<(ostream& out, SimplificationResult const& self);
};

inline ostream& operator<<(ostream& out, SimplificationResult const& self) 
{
  return self.match(
      [&](Kernel::Clause const* const& self) -> ostream&
      { return out << pretty(self); },

      [&](SimplificationAlternative const& self)  -> ostream&
      { return out << pretty(self.lhs) << " or " << pretty(self.rhs); });
}

inline bool SimplificationResult::matches(const SimplificationTester& simpl, Kernel::Clause const& result)
{
  return match(
      [&](Kernel::Clause const*& self) 
      { return simpl.eq(&result, self); },

      [&](SimplificationAlternative& self) 
      { return self.lhs->matches(simpl, result) || self.rhs->matches(simpl, result); });
}



inline SimplificationResult anyOf(Kernel::Clause const& lhs) 
{ return SimplificationResult(lhs); }

template<class... As>
inline SimplificationResult anyOf(Kernel::Clause const& lhs, Kernel::Clause const& rhs, As... rest) 
{ return SimplificationResult(lhs, anyOf(rhs, rest...)); }

struct Success
{
  Kernel::Clause& input;
  // Kernel::Clause& expected;
  SimplificationResult expected;

  void run(const SimplificationTester& simpl) {
    auto res = simpl.simplify(&input);

    if (!res) {
      cout  << endl;
      cout << "[     case ]: " << pretty(input) << endl;
      cout << "[       is ]: NULL (indicates the clause is a tautology)" << endl;
      cout << "[ expected ]: " << pretty(expected) << endl;
      exit(-1);

    // } else if (!simpl.eq(res, &expected)) {
    } else if (!expected.matches(simpl, *res)) {
      cout  << endl;
      cout << "[     case ]: " << pretty(input) << endl;
      cout << "[       is ]: " << pretty(*res) << endl;
      cout << "[ expected ]: " << pretty(expected) << endl;
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
      cout << "[     case ]: " << pretty(input) << endl;
      cout << "[       is ]: " << pretty(*res) << endl;
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
