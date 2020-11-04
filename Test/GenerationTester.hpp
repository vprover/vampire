#ifndef __TEST__GENERATION_TESTER_HPP__
#define __TEST__GENERATION_TESTER_HPP__

/**
 * This file provides macros and classes used to write nice tests for simplification rules.
 *
 * Check out UnitTests/tGaussianElimination.cpp, to see how it is to be used.
 */

#include "Test/TestUtils.hpp"
#include "Kernel/Clause.hpp"
#include "Lib/Coproduct.hpp"
#include "Test/ClausePattern.hpp"

template<class C> 
struct Lib::ElementTypeInfo<std::initializer_list<C>> {
  using Type = C;
};

namespace Test {

template<class... As> void voidWrapper(As...) { }

int pushGenerated(
    Stack<ClausePattern>& out, 
    ClausePattern res) 
{
  out.push(std::move(res));
  return 0;
}

template<class... As>
Stack<ClausePattern> generated(As... as) 
{
  Stack<ClausePattern> out;
  voidWrapper(pushGenerated(out, as)...);
  return out;
}

namespace Generation {
struct TestCase;

template<class Rule>
class GenerationTester
{
  Rule _rule;

public:
  GenerationTester() 
    : _rule() 
  {}

  virtual bool eq(Kernel::Clause const* lhs, Kernel::Clause const* rhs) const 
  { return TestUtils::eqModAC(lhs, rhs); }

  friend struct TestCase;
};


struct TestCase
{
  Kernel::Clause* input;
  Stack<ClausePattern> generated;
  bool premiseRedundant;

  template<class Rule>
  void run(GenerationTester<Rule>& simpl) {
    auto res = simpl._rule.generateClauses(input);
    auto& sExp = generated;
    auto  sRes = Stack<Kernel::Clause*>::fromIterator(res.clauses);

    auto iExp = getArrayishObjectIterator<mut_ref_t>(sExp);
    auto iRes = getArrayishObjectIterator<mut_ref_t>(sRes);

    while (iRes.hasNext() && iExp.hasNext()) {
      auto& exp = iExp.next();
      auto& res = iRes.next();
      if (!exp.matches(simpl, res)) {
        cout  << endl;
        cout << "[     case ]: " << pretty(*input) << endl;
        cout << "[       is ]: " << pretty(sRes) << endl;
        cout << "[ expected ]: " << pretty(sExp) << endl;
        exit(-1);
      }
    }

    if (premiseRedundant != res.premiseRedundant) {
        cout  << endl;
        cout << "[     case ]: " << pretty(*input) << endl;
        cout << "[       is ]: premise is" << ( res.premiseRedundant ? "" : " not" ) << " redundant"  << endl;
        cout << "[ expected ]: premise is" << (     premiseRedundant ? "" : " not" ) << " redundant"  << endl;
        exit(-1);
    }
  }
};

#define REGISTER_GEN_TESTER(t) using __GenerationTester = t;

#define TEST_GENERATION(name, ...)                                                                            \
        TEST_GENERATION_WITH_SUGAR(name, SIMPL_SUGAR, __VA_ARGS__) 

#define TEST_GENERATION_WITH_SUGAR(name, syntax_sugar, ...)                                                   \
  TEST_FUN(name) {                                                                                            \
    __GenerationTester tester;                                                                                 \
    _Pragma("GCC diagnostic push")                                                                            \
    _Pragma("GCC diagnostic ignored \"-Wunused\"")                                                            \
      syntax_sugar                                                                                            \
    _Pragma("GCC diagnostic pop")                                                                             \
    auto test = __VA_ARGS__; \
    test.run(tester);                                                                                   \
  }                                                                                                           \

} // namespace Simplification

} // namespace Test

#endif // __TEST__GENERATION_TESTER_HPP__
