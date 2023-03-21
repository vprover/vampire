/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Forwards.hpp"
#include "Indexing/IndexManager.hpp"
#include "Indexing/LiteralIndex.hpp"
#include "Indexing/LiteralSubstitutionTree.hpp"
#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Inferences/BinaryInferenceEngine.hpp"
#include "Kernel/Ordering.hpp"

#include "Test/GenerationTester.hpp"
#include "Lib/Reflection.hpp"

using namespace Kernel;
using namespace Inferences;
using namespace Test;
using namespace Indexing;

class SimpleBinaryResolution {
public:
  static constexpr unsigned DEBUG_LEVEL = 0;


  struct Lhs 
  {
    Clause* cl;
    unsigned literalIndex;

    using Key = Literal*;

    Literal* key() const 
    { return Literal::positiveLiteral((*cl)[literalIndex]); }

    Clause* clause() const 
    { return cl; }

    friend std::ostream& operator<<(std::ostream& out, Lhs const& self)
    { return out << *self.cl<< "[" << self.literalIndex << "]"; }

    auto asTuple() const -> decltype(auto)
    { return std::tie(cl, literalIndex); }

    IMPL_COMPARISONS_FROM_TUPLE(Lhs);
  };

  struct Rhs 
  {
    Clause* cl;
    unsigned literalIndex;

    using Key = Literal*;

    Literal* key() const 
    { return (*cl)[literalIndex]; }

    Clause* clause() const 
    { return cl; }

    friend std::ostream& operator<<(std::ostream& out, Rhs const& self)
    { return out << *self.cl << "[" << self.literalIndex << "]"; }

    auto asTuple() const -> decltype(auto)
    { return std::tie(cl, literalIndex); }

    IMPL_COMPARISONS_FROM_TUPLE(Rhs);
  };


  using Matching = BinInfMatching::Unification<Lhs, Rhs>;

  IndexType indexType() const
  { return Indexing::SIMPLE_BINARY_RESOLUTION; }

  VirtualIterator<Lhs> iterLhs(Clause* cl) const
  {
    return pvi(range(0, cl->numSelected())
      .filter([cl](auto i) { return !(*cl)[i]->isEquality(); })
      .filter([cl](auto i) { return (*cl)[i]->isNegative(); })
      .map([cl](auto i) { return Lhs { .cl = cl, .literalIndex = i, }; }));
  };

  VirtualIterator<Rhs> iterRhs(Clause* cl) const
  {
    return pvi(range(0, cl->numSelected())
      .filter([cl](auto i) { return !(*cl)[i]->isEquality(); })
      .filter([cl](auto i) { return (*cl)[i]->isPositive(); })
      .map([cl](auto i) { return Rhs { .cl = cl, .literalIndex = i, }; }));
  }

  Clause* apply(
      Lhs const& lhs, bool lRes,
      Rhs const& rhs, bool rRes,
      ResultSubstitution& subs
      ) const
  {

    auto lhsLits = range(0, lhs.clause()->size())
      .filter([&](auto i) { return i != lhs.literalIndex; })
      .map([&](auto i){ 
          auto lit = (*lhs.clause())[i];
          return subs.apply(lit, lRes);
      });

    auto rhsLits = range(0, rhs.clause()->size())
      .filter([&](auto i) { return i != rhs.literalIndex; })
      .map([&](auto i){ 
          auto lit = (*rhs.clause())[i];
          return subs.apply(lit, rRes);
      });

    return Clause::fromIterator(
        concatIters(lhsLits, rhsLits), 
        Inference(GeneratingInference2(InferenceRule::SIMPLE_BINARY_RESOLUTION, lhs.clause(), rhs.clause())));
  }
};


Stack<std::function<Indexing::Index*()>> myRuleIndices()
{ return Stack<std::function<Indexing::Index*()>>{
  []() -> Index* { return new BinInfIndex<SimpleBinaryResolution>(); }
  }; }

SimpleBinaryResolution myRule()
{ return SimpleBinaryResolution(); }

#define MY_SYNTAX_SUGAR                                                                   \
                                                                                          \
  DECL_VAR(x, 0)                                                                          \
  DECL_VAR(y, 1)                                                                          \
  DECL_VAR(z, 2)                                                                          \
                                                                                          \
  DECL_SORT(s)                                                                            \
                                                                                          \
  DECL_CONST(a, s)                                                                        \
  DECL_CONST(b, s)                                                                        \
  DECL_CONST(c, s)                                                                        \
                                                                                          \
  DECL_FUNC(f, {s}, s)                                                                    \
  DECL_FUNC(g, {s}, s)                                                                    \
  DECL_FUNC(f2, {s,s}, s)                                                                 \
  DECL_FUNC(g2, {s,s}, s)                                                                 \
                                                                                          \
  DECL_PRED(p, {s})                                                                       \
  DECL_PRED(q, {s})                                                                       \
  DECL_PRED(p2, {s, s})                                                                   \
  DECL_PRED(q2, {s,s})                                                                    \
               

REGISTER_GEN_TESTER(Test::Generation::GenerationTester<BinaryInferenceEngine<SimpleBinaryResolution>>(BinaryInferenceEngine<SimpleBinaryResolution>(myRule())))

/////////////////////////////////////////////////////////
// Basic tests
//////////////////////////////////////

TEST_GENERATION(basic01,
    Generation::SymmetricTest()
      .indices(myRuleIndices())
      .inputs  ({ clause({ selected( p(a)  ), p(b)  }) 
                , clause({ selected( ~p(x) )        }) })
      .expected(exactly(
            clause({ p(b)  }) 
      ))
    )

TEST_GENERATION(basic02,
    Generation::SymmetricTest()
      .indices(myRuleIndices())
      .inputs  ({ clause({ selected( ~p(a)  ), p(b)  }) 
                , clause({ selected( p(x) )        }) })
      .expected(exactly(
            clause({ p(b)  }) 
      ))
    )

TEST_GENERATION(basic03,
    Generation::SymmetricTest()
      .indices(myRuleIndices())
      .inputs  ({ clause({ selected( ~p(a) ), p(b)  }) 
                , clause({ selected(  p(b) )        }) })
      .expected(exactly(     /* nothing */             ))
    )


TEST_GENERATION(basic04,
    Generation::SymmetricTest()
      .indices(myRuleIndices())
      .inputs  ({ clause({ selected( p(a)  ), p(b)  }) 
                , clause({ selected( p(x) )        }) })
      .expected(exactly(     /* nothing */             ))
    )

TEST_GENERATION(basic05,
    Generation::SymmetricTest()
      .indices(myRuleIndices())
      .inputs  ({ clause({ selected( ~p(a)  )  }) 
                , clause({ selected( p(x) )        }) })
      .expected(exactly( clause({ })         ))
    )

TEST_GENERATION(basic06,
    Generation::SymmetricTest()
      .indices(myRuleIndices())
      .inputs  ({ clause({ selected( ~p(f2(x, b)) ), q(f(x)) }) 
                , clause({ selected(  p(f2(a, x)) ), q(g(x)) }) 
                }) 
      .expected(exactly( clause({ q(f(a)), q(g(b)) })         ))
    )

TEST_GENERATION(basic07,
    Generation::SymmetricTest()
      .indices(myRuleIndices())
      .inputs  ({ clause({ selected(  p(f2(x, b)) ), q(f(x)) }) 
                , clause({ selected(  p(f2(a, x)) ), q(g(x)) }) 
                }) 
      .expected(exactly( /* nothing */ ))
    )


TEST_GENERATION(basic08,
    Generation::SymmetricTest()
      .indices(myRuleIndices())
      .inputs  ({ clause({ selected(  p(f2(x, b)) ), q(f(x)) }) 
                , clause({ selected( ~p(f2(a, x)) ), q(g(x)) }) 
                }) 
      .expected(exactly( clause({ q(f(a)), q(g(b)) })         ))
    )
