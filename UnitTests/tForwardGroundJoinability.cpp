/*
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
#include "Test/TestUtils.hpp"
#include "Test/ForwardSimplificationTester.hpp"

#include "Kernel/Ordering.hpp"

#include "Indexing/CodeTreeInterfaces.hpp"

#include "Inferences/ForwardGroundJoinability.hpp"

using namespace std;
using namespace Kernel;
using namespace Inferences;
using namespace Test;

namespace TestForwardGroundJoinability {

Stack<Index*> getIndices(const Ordering& ord, const Options& opt) {
  return { new DemodulationLHSIndex(new CodeTreeTIS(), ord, opt) };
}

#define MY_SYNTAX_SUGAR                                                                    \
  DECL_DEFAULT_VARS                                                                        \
  DECL_SORT(s)                                                                             \
  DECL_FUNC(f, {s, s}, s)

// // no simplification should happen
// TEST_FW_SIMPLIFY(test_1,
//     ForwardSimplification::TestCase()
//       .rule(new ForwardGroundJoinability())
//       .input(    clause({ f(f(x,y),z) == f(f(y,x),z) }))
//       .indices(&getIndices)
//     )

TEST_FW_SIMPLIFY(test_2,
    ForwardSimplification::TestCase()
      .rule(new ForwardGroundJoinability())
      .input(    clause({ f(f(x,y),z) == f(f(y,x),z) }))
      .context({ clause({ f(x,y) == f(y,x) }) })
      .indices(&getIndices)
      .expected( nullptr )
    )

TEST_FW_SIMPLIFY(test_3,
    ForwardSimplification::TestCase()
      .rule(new ForwardGroundJoinability())
      .input(    clause({ f(f(x,y),z) != f(f(y,x),z) }))
      .context({ clause({ f(x,y) == f(y,x) }) })
      .indices(&getIndices)
      .expected( clause({}) )
    )

TEST_FW_SIMPLIFY(test_4,
    ForwardSimplification::TestCase()
      .rule(new ForwardGroundJoinability())
      .input(    clause({ f(f(x,y),z) != f(y,f(z,x)) }))
      .context({
        clause({ f(x,y) == f(y,x) }),
        clause({ f(x,f(y,z)) == f(f(x,y),z) }),
        clause({ f(x,f(y,z)) == f(y,f(x,z)) }),
      })
      .indices(&getIndices)
      .expected( clause({}) )
    )

TEST_FW_SIMPLIFY(test_5,
    ForwardSimplification::TestCase()
      .rule(new ForwardGroundJoinability())
      .input(    clause({ f(f(f(x,y),z),x) != f(f(y,f(x,x)),z) }))
      .context({
        clause({ f(x,y) == f(y,x) }),
        clause({ f(x,f(y,z)) == f(f(x,y),z) }),
        clause({ f(x,f(y,z)) == f(y,f(x,z)) }),
      })
      .indices(&getIndices)
      .expected( clause({}) )
    )

TEST_FW_SIMPLIFY(test_6,
    ForwardSimplification::TestCase()
      .rule(new ForwardGroundJoinability())
      .input(    clause({ f(f(x,y),z) == f(y,f(z,x)) }))
      .context({
        clause({ f(x,y) == f(y,x) }),
        clause({ f(x,f(y,z)) == f(f(x,y),z) }),
        clause({ f(x,f(y,z)) == f(y,f(x,z)) }),
      })
      .indices(&getIndices)
      .expected( nullptr )
    )

TEST_FW_SIMPLIFY(test_7,
    ForwardSimplification::TestCase()
      .rule(new ForwardGroundJoinability())
      .input(    clause({ f(f(f(x,y),z),x) == f(f(y,f(x,x)),z) }))
      .context({
        clause({ f(x,y) == f(y,x) }),
        clause({ f(x,f(y,z)) == f(f(x,y),z) }),
        clause({ f(x,f(y,z)) == f(y,f(x,z)) }),
      })
      .indices(&getIndices)
      .expected( nullptr )
    )

} // TestForwardGroundJoinability