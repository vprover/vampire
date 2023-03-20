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
#include "Inferences/BinaryInferenceEngine.hpp"
#include "Kernel/Ordering.hpp"

#include "Test/GenerationTester.hpp"

using namespace Kernel;
using namespace Inferences;
using namespace Test;
using namespace Indexing;

class SimpleBinaryResolution {
public:
  static constexpr unsigned DEBUG_LEVEL = 0;

  struct Lhs 
  {
    Clause* clause;
    unsigned literalIndex;

    Literal* key() const 
    { return (*clause)[literalIndex]; }

    friend std::ostream& operator<<(std::ostream& out, Lhs const& self)
    { return out << *self.clause << "[" << self.literalIndex << "]"; }
  };

  struct Rhs 
  {
    Clause* clause;
    unsigned literalIndex;

    Literal* key() const 
    { return (*clause)[literalIndex]; }

    friend std::ostream& operator<<(std::ostream& out, Rhs const& self)
    { return out << *self.clause << "[" << self.literalIndex << "]"; }
  };


  IndexType lhsIndexType() const;
  IndexType rhsIndexType() const;

  VirtualIterator<Lhs> iterLhs(Clause* cl) const
  {
    return pvi(range(0, cl->numSelected())
      .filter([cl](auto i) { return !(*cl)[i]->isEquality(); })
      .filter([cl](auto i) { return (*cl)[i]->isNegative(); })
      .map([cl](auto i) { return Lhs { .clause = cl, .literalIndex = i, }; }));
  };

  VirtualIterator<Rhs> iterRhs(Clause* cl) const
  {
    return pvi(range(0, cl->numSelected())
      .filter([cl](auto i) { return !(*cl)[i]->isEquality(); })
      .filter([cl](auto i) { return (*cl)[i]->isPositive(); })
      .map([cl](auto i) { return Rhs { .clause = cl, .literalIndex = i, }; }));
  }

  Clause* apply(
      Lhs const& lhs, unsigned lhsVarBank,
      Rhs const& rhs, unsigned rhsVarBank,
      RobSubstitution& uwa
      ) const;
};

Stack<std::function<Indexing::Index*()>> myRuleIndices()
{ return Stack<std::function<Indexing::Index*()>>{
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
      .inputs  ({ clause({ selected( 3 * f(x) - 4 == 0 )  }) 
                , clause({ selected(     3 * f(x) >  0 )  }) })
      .expected(exactly(
            clause({ 3 * frac(4,3) > 0  })
      ))
    )
