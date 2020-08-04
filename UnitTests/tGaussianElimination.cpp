
#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Indexing/TermSharing.hpp"
#include "Inferences/GaussianVariableElimination.hpp"
#include "Inferences/InterpretedEvaluation.hpp"
#include "Kernel/Ordering.hpp"
#include "Inferences/PolynomialNormalization.hpp"

#include "Test/SyntaxSugar.hpp"
#include "Test/TestUtils.hpp"

#define UNIT_ID GaussianVariableElimination
UT_CREATE;

using namespace std;
using namespace Kernel;
using namespace Inferences;
using namespace Test;

Clause* exhaustiveGve(Clause* in) {

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
  static GaussianVariableElimination inf = GaussianVariableElimination();
  // static InterpretedEvaluation ev = InterpretedEvaluation(false, ord);
  static PolynomialNormalization ev(ord);
  Clause* last = ev.simplify(in);
  Clause* latest = ev.simplify(in);
  do {
    last = latest;
    latest = ev.simplify(inf.simplify(last));
  } while (latest != last);
  return latest;
}


void test_eliminate_na(Clause& toSimplify) {
  auto res = exhaustiveGve(&toSimplify);
  if (res != &toSimplify ) {
    cout  << endl;
    cout << "[     case ]: " << toSimplify.toString() << endl;
    cout << "[       is ]: " << res->toString() << endl;
    cout << "[ expected ]: < nop >" << endl;
    exit(-1);
  }
}

void test_eliminate(Clause& toSimplify, const Clause& expected) {
  auto res = exhaustiveGve(&toSimplify);
  if (!res || !TestUtils::eqModAC(res, &expected)) {
    cout  << endl;
    cout << "[     case ]: " << toSimplify.toString() << endl;
    cout << "[       is ]: " << res->toString() << endl;
    cout << "[ expected ]: " << expected.toString() << endl;
    exit(-1);
  }
}

#define SUGAR \
    THEORY_SYNTAX_SUGAR(REAL) \
      _Pragma("GCC diagnostic push") \
      _Pragma("GCC diagnostic ignored \"-Wunused\"") \
        THEORY_SYNTAX_SUGAR_FUN(f, 1) \
        THEORY_SYNTAX_SUGAR_PRED(p, 1) \
      _Pragma("GCC diagnostic pop") \
 
#define TEST_ELIMINATE(name, toSimplify, expected) \
  TEST_FUN(name) { \
   SUGAR \
   test_eliminate((toSimplify),(expected)); \
  }

#define TEST_ELIMINATE_NA(name, toSimplify) \
  TEST_FUN(name) { \
    SUGAR \
    test_eliminate_na((toSimplify)); \
  }

TEST_ELIMINATE(gve_test_1
    , clause({  3 * x != 6, x < y  })
    , clause({  2 < y  })
    )

TEST_ELIMINATE_NA(gve_test_2
    , clause({ 3 * x == 6, x < y })
    )

TEST_ELIMINATE(gve_test_3
    , clause({  3 * x != 6, x < x  })
    , clause({  /* 2 < 2 */  }) 
    )

  // 2x + y = x + y ==> 0 = 2x + y - x - y ==> 0 = x
TEST_ELIMINATE(gve_test_4
    , clause({  2 * x + y != x + y, p(x) })
    , clause({  p(0)  })
    )

TEST_ELIMINATE(gve_test_uninterpreted
    , clause({  3 * f(x) != y, x < y  })
    , clause({  x < 3 * f(x)  })
    )

  // x!=4 \/ x+y != 5 \/ C[x]
  //         4+y != 5 \/ C[4]
  //                     C[4]
TEST_ELIMINATE(gve_test_multiplesteps_1
    , clause({  x != 4, x + y != 5, x < f(x)  })
    , clause({  4 < f(4)  })
    )

  // x!=4 \/ x+y != 5 \/ C[x,y]
  //         4+y != 5 \/ C[4,y]
  //                     C[4,1]
TEST_ELIMINATE(gve_test_multiplesteps_2
    , clause({  x != 4, x + y !=  5, x < f(y)  })
    , clause({  4 < f(1)  })
    )

  // x  !=4 \/ x+y != 5 \/ C[x]
  // 5-y!=4             \/ C[5-y]
  //                    \/ C[5]


