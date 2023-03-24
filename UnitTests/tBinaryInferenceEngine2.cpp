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
#include "Debug/Output.hpp"

#include "Test/GenerationTester.hpp"
#include "Lib/Reflection.hpp"

using namespace Kernel;
using namespace Inferences;
using namespace Test;
using namespace Indexing;


class SimpleSubsumptionResolution {
public:
  static constexpr unsigned DEBUG_LEVEL = 1;

  struct Lhs 
  {
    Clause* cl;
    unsigned literalIndex;

    using Key = Literal*;

    Literal* key() const 
    { return Literal::complementaryLiteral((*cl)[literalIndex]); }

    Clause* clause() const 
    { return cl; }

    friend std::ostream& operator<<(std::ostream& out, Lhs const& self)
    { return out << *self.cl << "[" << self.literalIndex << "]"; }

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


  using Matching = BinInfMatching::RightInstanceOfLeft<Lhs, Rhs>;

  IndexType indexType() const
  { return Indexing::SIMPLE_SUBSUMPTION_RESOLUTION; }

  VirtualIterator<Lhs> iterLhs(Clause* cl) const
  {
    return pvi(range(0, cl->numSelected())
      .map([cl](auto i) { return Lhs { .cl = cl, .literalIndex = i, }; }));
  }

  VirtualIterator<Rhs> iterRhs(Clause* cl) const
  {
    return pvi(range(0, cl->numSelected())
      .map([cl](auto i) { return Rhs { .cl = cl, .literalIndex = i, }; }));
  }

  RuleApplicationResult apply(
      Lhs const& lhs, bool lRes,
      Rhs const& rhs, bool rRes,
      ResultSubstitution& subs
      ) const
  {

    auto rhsLits = [&]() {  
      return range(0, rhs.clause()->size())
        .filter([&](auto i) { return i != rhs.literalIndex; })
        .map([&](auto i)
            { return (*rhs.clause())[i]; });
    };

    auto lhsLits = [&]() {
      return range(0, lhs.clause()->size())
        .filter([&](auto i) { return i != lhs.literalIndex; })
        .map([&](auto i)
            { return subs.apply((*lhs.clause())[i], lRes); });
    };

    for (auto lit : lhsLits()) {
       if (rhsLits().find([&](auto r) { return r == lit; })
                        .isNone()) {
         return RuleApplicationResult::fail(*this, *lit, " is not contained in ", outputInterleaved(" | ", rhsLits()));
       }
    }

    return Clause::fromIterator(
        rhsLits(),
        Inference(SimplifyingInference2(InferenceRule::SIMPLE_SUBSUMPTION_RESOLUTION, lhs.clause(), rhs.clause())));
  }
};



Stack<std::function<Indexing::Index*()>> simplSubResoIndices()
{ return Stack<std::function<Indexing::Index*()>>{
  []() -> Index* { return new BinInfIndex<SimpleSubsumptionResolution>(); }
  }; }

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
               

REGISTER_GEN_TESTER(Test::Generation::GenerationTester<BinaryInferenceEngine<SimpleSubsumptionResolution>>(BinaryInferenceEngine<SimpleSubsumptionResolution>(SimpleSubsumptionResolution())))

/////////////////////////////////////////////////////////
// Basic tests
//////////////////////////////////////

TEST_GENERATION(basic01,
    Generation::SymmetricTest()
      .indices(simplSubResoIndices())
      .inputs  ({ clause({ selected( p(a)  ), p(b)  }) 
                , clause({ selected( ~p(x) )        }) })
      .expected(exactly(
            clause({ p(b)  }) 
      ))
      // .premiseRedundant(true)
    )

TEST_GENERATION(basic02,
    Generation::SymmetricTest()
      .indices(simplSubResoIndices())
      .inputs  ({ clause({ selected( ~p(x)  ), p(b)  }) 
                , clause({ selected( p(a) )        }) })
      .expected(exactly(
          /* nothing */
      ))
      // .premiseRedundant(true)
    )

TEST_GENERATION(basic03,
    Generation::SymmetricTest()
      .indices(simplSubResoIndices())
      .inputs  ({ clause({ selected( ~p(a) ), p(b)  }) 
                , clause({ selected(  p(x) ), p(c)  }) })
      .expected(exactly(     /* nothing */             ))
      // .premiseRedundant(true)
    )


TEST_GENERATION(basic04,
    Generation::SymmetricTest()
      .indices(simplSubResoIndices())
      .inputs  ({ clause({ selected(  p(f(a)) ), p(a), p(b)  }) 
                , clause({ selected( ~p(f(x)) ), p(x)        }) })
      .expected(exactly(
            clause({ p(a), p(b)  }) 
      ))
      // .premiseRedundant(true)
    )
