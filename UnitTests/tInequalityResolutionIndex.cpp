/*
 * File tInequalityResolutionIndex.cpp.
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
#include "Indexing/TermSharing.hpp"
#include "Inferences/InequalityResolution.hpp"
#include "Inferences/InterpretedEvaluation.hpp"
#include "Kernel/Ordering.hpp"
#include "Inferences/PolynomialEvaluation.hpp"
#include "Inferences/Cancellation.hpp"

#include "Test/SyntaxSugar.hpp"
#include "Test/TestUtils.hpp"
#include "Lib/Coproduct.hpp"
#include "Test/SimplificationTester.hpp"
#include "Test/TermIndexTester.hpp"
#include "Kernel/KBO.hpp"
#include "Indexing/TermSubstitutionTree.hpp"

using namespace std;
using namespace Kernel;
using namespace Inferences;
using namespace Test;
using Test::TermIndex::termQueryResult;
using Test::TermIndex::subs;

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////// TEST CASES 
/////////////////////////////////////

#define MY_SYNTAX_SUGAR                                                                                       \
  NUMBER_SUGAR(Rat)                                                                                           \
  DECL_DEFAULT_VARS                                                                                           \
  DECL_FUNC(f, {Rat}, Rat)                                                                                    \
  DECL_CONST(a, Rat)                                                                                          \
  DECL_CONST(b, Rat)                                                                                          \


TERM_INDEX_TEST_SET_DEFAULT(withConstraints, true);
TERM_INDEX_TEST_SET_DEFAULT(index, new InequalityResolutionIndex(new TermSubstitutionTree(), *new KBO(KBO::testKBO())));

TEST_TERM_INDEX(test01,
    TermIndex::TestCase()
      .contents ({ 
                  clause({  2 * a + 3 * b > 0  }),
      })
      .query (  3 * a )
      .expected({
          termQueryResult()
            .term        (   2 * a               )
            .literal     (   2 * a + 3 * b > 0   )
            .clause      ({  2 * a + 3 * b > 0  })
            .substitution({ })
            .constraints ({ })
      })
    )

TEST_TERM_INDEX(test02,
    TermIndex::TestCase()
      .contents ({ 
                  clause({  2 * a + 3 * b > 0  }),
      })
      .query (  3 * b )
      .expected({
          termQueryResult()
            .term        (   3 * b               )
            .substitution({ })
            .constraints ({ })
      })
    )

TEST_TERM_INDEX(test03,
    TermIndex::TestCase()
      .contents ({ 
                  clause({  2 * a + 3 * b > 0  }),
      })
      .query (  3 * b )
      .expected({
          termQueryResult()
            .term        (   3 * b               )
            .substitution({ })
            .constraints ({ })
      })
    )

TEST_TERM_INDEX(test04,
    TermIndex::TestCase()
      .contents ({ 
                  clause({      f(a) > 0  }),
                  clause({  2 * f(b) > 0  }),
      })
      .query (  3 * b )
      .expected({ /* nothing */ })
    )

TEST_TERM_INDEX(test05,
    TermIndex::TestCase()
      .contents ({ 
                  clause({      f(a) > 0  }),
                  clause({  2 * f(b) > 0  }),
      })
      .query (  f(x) )
      .expected({

          termQueryResult()
            .term        ( f(a) )
            .substitution({ subs(x, a) })
            .constraints ({ }),

          termQueryResult()
            .term        ( f(b) )
            .substitution({ subs(x, b) })
            .constraints ({ }),

      })
    )

TEST_TERM_INDEX(test06,
    TermIndex::TestCase()
      .contents ({ 
                  clause({  f(b + x + y) > 0  }),
      })
      .query (  f(a + z) )
      .expected({

          termQueryResult()
            .term        ( f(b + x + y) )
            .substitution({  })
            .constraints ({ b + x + y == a + z }),

      })
    )

TEST_TERM_INDEX(test07,
    TermIndex::TestCase()
      .contents ({ 
                  clause({  f(b + x + y) + f(a + b) > 0  }),
      })
      .query (  f(a + z) )
      .expected({

          termQueryResult()
            .term        ( f(b + x + y) )
            .substitution({  })
            .constraints ({ b + x + y == a + z }),

          termQueryResult()
            .term        ( f(a + b) )
            .substitution({ subs(z, a)  })
            .constraints ({  }),

      })
    )
