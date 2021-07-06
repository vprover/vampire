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
#include "Indexing/TermSharing.hpp"
#include "Inferences/IRC/FwdDemodulationModLA.hpp"
#include "Inferences/IRC/BwdDemodulationModLA.hpp"
#include "Inferences/InterpretedEvaluation.hpp"
#include "Kernel/Ordering.hpp"
#include "Inferences/PolynomialEvaluation.hpp"
#include "Inferences/Cancellation.hpp"

#include "Test/SyntaxSugar.hpp"
#include "Test/TestUtils.hpp"
#include "Lib/Coproduct.hpp"
#include "Test/SimplificationTester.hpp"
#include "Test/FwdBwdSimplificationTester.hpp"
#include "Kernel/KBO.hpp"
#include "Indexing/TermSubstitutionTree.hpp"
#include "Inferences/PolynomialEvaluation.hpp"

// TODO rename FwdBwdSimplificationTester to SimplificationTester and SimplificationTester to  ImmediatesSimplificationTester

using namespace std;
using namespace Kernel;
using namespace Inferences;
using namespace Test;
using namespace Indexing;
using namespace Inferences::IRC;

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////// TEST CASES 
/////////////////////////////////////

#define SUGAR(Num)                                                                                            \
  NUMBER_SUGAR(Num)                                                                                           \
  DECL_DEFAULT_VARS                                                                                           \
  DECL_FUNC(f, {Num}, Num)                                                                                    \
  DECL_FUNC(g, {Num}, Num)                                                                                    \
  DECL_CONST(a, Num)                                                                                          \
  DECL_CONST(b, Num)                                                                                          \
  DECL_CONST(c, Num)                                                                                          \
  DECL_PRED(p, {Num})                                                                                         \
  DECL_PRED(r, {Num,Num})                                                                                     \

#define MY_SYNTAX_SUGAR SUGAR(Rat)

#define UWA_MODE Options::UnificationWithAbstraction::IRC1

Indexing::Index* ircDemodulationIndex() 
{ UNIMPLEMENTED }
// { return new Indexing::DemodulationIndex(new TermSubstitutionTree(UWA_MODE, true)); }

FwdDemodulationModLA* testFwdDemodulationModLA()
{ UNIMPLEMENTED }
// { return FwdDemodulationModLA(testIrcState(UWA_MODE)); }

BwdDemodulationModLA* testBwdDemodulationModLA()
{ UNIMPLEMENTED }
// { return new Indexing::DemodulationIndex(new TermSubstitutionTree(UWA_MODE, true)); }

// REGISTER_SIMPL_TESTER(Test::FwdBwdSimplification::Tester<FwdDemodulationModLA, BwdDemodulationModLA>(testFwdDemodulationModLA(), testBwdDemodulationModLA()))
//
BUILDER_SET_DEFAULT(FwdBwdSimplification::TestCase, fwd, testFwdDemodulationModLA());
BUILDER_SET_DEFAULT(FwdBwdSimplification::TestCase, bwd, testBwdDemodulationModLA());

/////////////////////////////////////////////////////////
// Basic tests
//////////////////////////////////////

TEST_SIMPLIFICATION(basic01,
    FwdBwdSimplification::TestCase()
      .indices({ ircDemodulationIndex() })
      .simplifyWith({    clause(   { 0 == f(a) - a  }   ) })
      .toSimplify  ({    clause(   { p(f(a))        }   ) })
      .expected(    {    clause(   { p(  a )        }   ) })
      .justifications({  clause(   { 0 == f(a) - a  }   )}) // TODO default justifications to everything
    )


TEST_SIMPLIFICATION(basic02,
    FwdBwdSimplification::TestCase()
      .indices({ ircDemodulationIndex() })
      .simplifyWith({    clause(   { 0 == f(a) - a   }   )
                    ,    clause(   { 0 == g(b,a) - b }   ) })
      .toSimplify  ({    clause(   { r(f(a), f(b))   }   ) })
      .expected(    {    clause(   { r(  a , f(b))   }   ) })
      .justifications({  clause(   {  0 == f(a) - a  }   ) })
    )

TEST_SIMPLIFICATION(basic03,
    FwdBwdSimplification::TestCase()
      .indices({ ircDemodulationIndex() })
      .simplifyWith({    clause(   { 0 == f(x) - x      }   ) })
      .toSimplify  ({    clause(   { r(f(a), f(b))      }   ) })
      .expected(    {    clause(   { r(  a , f(b))      }   ) })
      .justifications({  clause(   {  0 == f(x) - x     }   )}) // TODO default justifications to everything
    )

TEST_SIMPLIFICATION(basic04,
    FwdBwdSimplification::TestCase()
      .indices({ ircDemodulationIndex() })
      .simplifyWith({    clause(   { 0 == f(x) - x }   ) })
      .toSimplify  ({    clause(   { p(f(a))       }   ) , clause(   { p(f(b)) }   ) })
      .expected(    {    clause(   { p(  a )       }   ) , clause(   { p(  b ) }   ) })
      .justifications({  clause(   { 0 == f(x) - x }   )}) // TODO default justifications to everything
    )

TEST_SIMPLIFICATION(basic05,
    FwdBwdSimplification::TestCase()
      .indices({ ircDemodulationIndex() })
      .simplifyWith({    clause(   { 0 == f(a) - a }   ), clause(   { 0 == f(b) - b }   ) })
      .toSimplify  ({    clause(   { p(f(a)) }         ), clause(   { p(f(b)) }         ) })
      .expected(    {    clause(   { p(  a ) }         ), clause(   { p(  b ) }         ) })
      .justifications({  clause(   { 0 == f(a) - a }   ), clause(   { 0 == f(b) - b }   ) }) // TODO default justifications to everything
    )

TEST_SIMPLIFICATION(basic06,
    FwdBwdSimplification::TestCase()
      .indices({ ircDemodulationIndex() })
      .simplifyWith({    clause(   { 0 == f(a) - a }   ), clause(   { 0 == f(b) - b }   ) })
      .toSimplify  ({    clause(   { p(f(a)) }         ), clause(   { p(f(f(a))) }         ) })
      .expected(    {    clause(   { p(  a ) }         ), clause(   { p(  f(a) ) }         ) })
      .justifications({  clause(   { 0 == f(a) - a }   )}) // TODO default justifications to everything
    )

TEST_SIMPLIFICATION(basic07,
    FwdBwdSimplification::TestCase()
      .indices({ ircDemodulationIndex() })
      .simplifyWith({    clause(   { 0 == g(a, x) - x      }   ) })
      .toSimplify  ({    clause(   { p(g(a,b))             }   ) })
      .expected(    {    clause(   { p(    b )             }   ) })
      .justifications({  clause(   { 0 == g(a, x) - x      }   )  }) // TODO default justifications to everything
    )

TEST_SIMPLIFICATION(basic08,
    FwdBwdSimplification::TestCase()
      .indices({ ircDemodulationIndex() })
      .simplifyWith({    clause(   { 0 == g(a, x) - x      }   ) })
      .toSimplify  ({    clause(   { p(g(y,b))             }   ) })
      .expected(       { /* nothing */                     })
      .justifications({}) 
    )

