
#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Indexing/TermSharing.hpp"
#include "Inferences/GaussianVariableElimination.hpp"
#include "Inferences/InterpretedEvaluation.hpp"
#include "Kernel/Ordering.hpp"
#include "Inferences/PolynomialNormalization.hpp"

#include "Test/SyntaxSugar.hpp"
#include "Test/TestUtils.hpp"
#include "Lib/Coproduct.hpp"

#define UNIT_ID GaussianVariableElimination
UT_CREATE;

using namespace std;
using namespace Kernel;
using namespace Inferences;
using namespace Test;

class SimplificationTester
{
public:
  virtual Clause* simplify(Clause*) const = 0;

  virtual bool eq(Clause const* lhs, Clause const* rhs) const 
  {
    return TestUtils::eqModAC(lhs, rhs);
  }
};

struct SimplSuccess
{
  Clause& input;
  Clause& expected;

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
  Clause& input;

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



class GveSimplTester : public SimplificationTester
{
public:
  virtual Clause* simplify(Clause* in) const override {
    struct FakeOrdering : Kernel::Ordering {
      virtual Result compare(Literal* l, Literal* r) const override { 
        if (l == r) {
          return Kernel::Ordering::EQUAL; 
        } else {
          return Kernel::Ordering::LESS; 
        }
      }
      virtual Result compare(TermList, TermList) const override {ASSERTION_VIOLATION}
      virtual Comparison compareFunctors(unsigned, unsigned) const override {ASSERTION_VIOLATION}
    };
    static FakeOrdering ord;
    static GaussianVariableElimination gve = GaussianVariableElimination();
    static PolynomialNormalization eval(ord);

    /* applies gve and evaluation until they're not applicable anymore */
    Clause* last = eval.simplify(in);
    Clause* latest = eval.simplify(in);
    do {
      last = latest;
      latest = eval.simplify(gve.simplify(last));
    } while (latest != last);
    return latest;
  }
};

#define TEST_SIMPLIFY(name, ...) \
  TEST_FUN(name) { \
    SimplTester simpl; \
    SIMPL_SUGAR \
    __VA_ARGS__.run(simpl); \
  } \

using SimplTester = GveSimplTester;

#define SIMPL_SUGAR \
    THEORY_SYNTAX_SUGAR(REAL) \
      _Pragma("GCC diagnostic push") \
      _Pragma("GCC diagnostic ignored \"-Wunused\"") \
        THEORY_SYNTAX_SUGAR_FUN(f, 1) \
        THEORY_SYNTAX_SUGAR_PRED(p, 1) \
      _Pragma("GCC diagnostic pop") \

TEST_SIMPLIFY(gve_test_1,
    SimplSuccess {
      .input    = clause({  3 * x != 6, x < y  }),
      .expected = clause({  2 < y  }),
    })

TEST_SIMPLIFY(gve_test_2,
    NotApplicable {
      .input = clause({ 3 * x == 6, x < y }),
    })

TEST_SIMPLIFY(gve_test_3,
    SimplSuccess {
      .input    = clause({  3 * x != 6, x < x  }),
      .expected = clause({  /* 2 < 2 */  }),
    })

  // 2x + y = x + y ==> 0 = 2x + y - x - y ==> 0 = x
TEST_SIMPLIFY(gve_test_4,
    SimplSuccess {
      .input    = clause({  2 * x + y != x + y, p(x) }),
      .expected = clause({  p(0)  }),
    })

TEST_SIMPLIFY(gve_test_uninterpreted,
    SimplSuccess {
      .input    = clause({  3 * f(x) != y, x < y  }),
      .expected = clause({  x < 3 * f(x)  }),
    })

  // x!=4 \/ x+y != 5 \/ C[x]
  //         4+y != 5 \/ C[4]
  //                     C[4]
TEST_SIMPLIFY(gve_test_multiplesteps_1,
    SimplSuccess {
      .input    = clause({  x != 4, x + y != 5, x < f(x)  }),
      .expected = clause({  4 < f(4)  }),
    })

  // x!=4 \/ x+y != 5 \/ C[x,y]
  //         4+y != 5 \/ C[4,y]
  //                     C[4,1]
TEST_SIMPLIFY(gve_test_multiplesteps_2,
    SimplSuccess {
      .input    = clause({  x != 4, x + y !=  5, x < f(y)  }),
      .expected = clause({  4 < f(1)  }),
    })
