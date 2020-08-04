
#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Indexing/TermSharing.hpp"
#include "Inferences/GaussianVariableElimination.hpp"
#include "Inferences/InterpretedEvaluation.hpp"
#include "Kernel/Ordering.hpp"
#include "Inferences/PolynomialNormalization.hpp"

#define UNIT_ID GaussianVariableElimination
UT_CREATE;
using namespace std;
using namespace Kernel;
using namespace Inferences;

#include "Test/SyntaxSugar.hpp"


//TODO factor out
Clause& clause(std::initializer_list<Literal*> ls) { 
  static Inference testInf = Kernel::NonspecificInference0(UnitInputType::ASSUMPTION, InferenceRule::INPUT); 
  Clause& out = *new(ls.size()) Clause(ls.size(), testInf); 
  auto l = ls.begin(); 
  for (int i = 0; i < ls.size(); i++) { 
    out[i] = *l; 
    l++; 
  }
  return out; 
}

bool exactlyEq(const Clause& lhs, const Clause& rhs, const Stack<unsigned>& perm) {
  for (int j = 0; j < perm.size(); j++) {
    if (!Indexing::TermSharing::equals(lhs[j], rhs[perm[j]])) {
      return false;
    }
  }
  return true;
}


bool permEq(const Clause& lhs, const Clause& rhs, Stack<unsigned>& perm, unsigned idx) {
  if (exactlyEq(lhs, rhs, perm)) {
    return true;
  }
  for (int i = idx; i < perm.size(); i++) {
    swap(perm[i], perm[idx]);

    
    if (permEq(lhs,rhs, perm, idx+1)) return true;

    swap(perm[i], perm[idx]);
  }

  return false;
}

//TODO factor out
bool operator==(const Clause& lhs, const Clause& rhs) {
  if (lhs.size() != rhs.size()) return false;

  Stack<unsigned> perm;
  for (int i = 0; i<lhs.size(); i++) {
    perm.push(i);
  }
  return permEq(lhs, rhs, perm, 0);

}
bool operator!=(const Clause& lhs, const Clause& rhs) {
  return !(lhs == rhs);
}


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
  if (!res || *res != expected) {
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

TEST_ELIMINATE(test_1
    , clause({  3 * x != 6, x < y  })
    , clause({  2 < y  })
    )

TEST_ELIMINATE_NA(test_2
    , clause({ 3 * x == 6, x < y })
    )

TEST_ELIMINATE(test_3
    , clause({  3 * x != 6, x < x  })
    , clause({  /* 2 < 2 */  }) 
    )

  // 2x + y = x + y ==> 0 = 2x + y - x - y ==> 0 = x
TEST_ELIMINATE(test_4
    , clause({  2 * x + y != (x + y), p(x) })
    , clause({  p(0)  })
    )

  // 2x + y = x + y ==> 0 = 2x + y - x - y ==> 0 = x
// temporary commented out. working on new-eval branch already
// TEST_ELIMINATE(test_4
//     , clause({  neq(add(mul(2, x), y), add(x, y)), p(x) })
//     , clause({  p(0)  })
//     )

TEST_ELIMINATE(test_uninterpreted
    , clause({  3 * f(x) != y, x < y  })
    , clause({  x < 3 * f(x)  })
    )

  // x!=4 \/ x+y != 5 \/ C[x]
  //         4+y != 5 \/ C[4]
  //                     C[4]
TEST_ELIMINATE(test_multiplesteps_1
    , clause({  x != 4, x + y != 5, x < f(x)  })
    , clause({  4 < f(4)  })
    )

  // x!=4 \/ x+y != 5 \/ C[x,y]
  //         4+y != 5 \/ C[4,y]
  //                     C[4,1]
TEST_ELIMINATE(test_multiplesteps_2
    , clause({  x != 4, x + y !=  5, x < f(y)  })
    , clause({  4 < f(1)  })
    )

  // x  !=4 \/ x+y != 5 \/ C[x]
  // 5-y!=4             \/ C[5-y]
  //                    \/ C[5]


