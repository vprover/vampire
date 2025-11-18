/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#include "Inferences/AnswerLiteralProcessors.hpp"
#include "Inferences/ProofExtra.hpp"
#include "Kernel/Inference.hpp"
#include "Shell/AnswerLiteralManager.hpp"
#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"

#include "Test/SimplificationTester.hpp"

using namespace std;
using namespace Kernel;
using namespace Inferences;
using namespace Test;

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////// TEST UNIT INITIALIZATION
/////////////////////////////////////


#define MY_SYNTAX_SUGAR                                                                   \
  DECL_DEFAULT_VARS                                                                       \
  DECL_SORT(s)                                                                            \
  DECL_FUNC(f, {s}, s)                                                                    \
  DECL_FUNC(g, {s}, s)                                                                    \
  DECL_CONST(a, s)                                                                        \
  DECL_ANSWER_PRED (ans, {s})                                                             \
  DECL_PRED (p, {s})                                                                      \
  DECL_PRED (q, {s})                                                                      \

class SynthesisALProcessorTester : public Test::Simplification::SimplificationManyTester<SynthesisAnswerLiteralProcessor>
{
public:
  SynthesisALProcessorTester()
    : Test::Simplification::SimplificationManyTester<SynthesisAnswerLiteralProcessor>(SynthesisAnswerLiteralProcessor())
  {
    env.options->set("question_answering", "synthesis");
  }
  virtual Option<ClauseIterator> simplifyMany(Kernel::Clause* in) override 
  { return _rule.simplifyMany(in); }
};

REGISTER_SIMPL_MANY_TESTER(SynthesisALProcessorTester)

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////// TEST CASES
/////////////////////////////////////

TEST_SIMPLIFY_MANY(no_answer_literals,
    Simplification::NotApplicableMany()
      .input( clause({ p(x), q(a) }) )
    )

TEST_SIMPLIFY_MANY(one_answer_literal,
    Simplification::NotApplicableMany()
      .input( clause({ p(x), ans(y) }) )
    )

TEST_SIMPLIFY_MANY(two_answer_literals_generic_inference,
    Simplification::NotApplicableMany()
      .input( clause({ p(x), ans(y), ans(x) }) )
    )

TEST_SIMPLIFY_MANY(three_answer_literals,
    Simplification::NotApplicableMany()
      .input( clause({ p(x), ans(y), ans(x), ans(a) }) )
    )

TEST_SIMPLIFY_MANY(three_answer_literals_binary_resolution,
    Clause* cl = clause({ p(x), ans(y), ans(x), ans(a) }, Inference(Kernel::NonspecificInference0(UnitInputType::ASSUMPTION, InferenceRule::RESOLUTION)));
    Simplification::NotApplicableMany()
      .input(cl)
    )

TEST_SIMPLIFY_MANY(two_answer_literals_binary_resolution,
    Literal *al1 = ~ans(f(x)), *al2 = ~ans(a), *cond = q(a);
    Clause* cl = clause({ p(x), al1, al2 }, Inference(Kernel::NonspecificInference0(UnitInputType::ASSUMPTION, InferenceRule::RESOLUTION)));
    env.proofExtra.insert(cl, new Inferences::TwoLiteralInferenceExtra(
      q(a),
      ~q(a),
      cond,
      al1,
      al2
    ));
    Clause* exp1 = clause({ p(x), static_cast<Shell::SynthesisALManager*>(Shell::SynthesisALManager::getInstance())->makeITEAnswerLiteral(cond, al1, al2) });
    Clause* exp2 = clause({ p(x), f(x) != a, al1 });
    Simplification::SuccessMany()
      .input(cl)
      .expected({ exp1, exp2 })
    )

TEST_SIMPLIFY_MANY(two_answer_literals_superposition,
    Literal *al1 = ~ans(f(x)), *al2 = ~ans(a), *cond = g(a)==f(x);
    Clause* cl = clause({ p(g(a)), al1, al2 }, Inference(Kernel::NonspecificInference0(UnitInputType::ASSUMPTION, InferenceRule::SUPERPOSITION)));
    env.proofExtra.insert(cl, new Inferences::TwoLiteralRewriteInferenceExtra(
      p(f(x)),
      cond,
      g(a),
      f(x),
      cond,
      al1,
      al2
    ));
    Clause* exp1 = clause({ p(g(a)), static_cast<Shell::SynthesisALManager*>(Shell::SynthesisALManager::getInstance())->makeITEAnswerLiteral(cond, al1, al2) });
    Clause* exp2 = clause({ p(g(a)), f(x) != a, al1 });
    Simplification::SuccessMany()
      .input(cl)
      .expected({ exp1, exp2 })
    )

TEST_SIMPLIFY_MANY(twice_the_same_answer_literal_binary_resolution,
    Literal *al1 = ~ans(f(x)), *al2 = ~ans(f(x)), *cond = q(a);
    Clause* cl = clause({ p(x), al1, al2 }, Inference(Kernel::NonspecificInference0(UnitInputType::ASSUMPTION, InferenceRule::RESOLUTION)));
    env.proofExtra.insert(cl, new Inferences::TwoLiteralInferenceExtra(
      q(a),
      ~q(a),
      cond,
      al1,
      al2
    ));
    Simplification::SuccessMany()
      .input(cl)
      .expected({ clause({ p(x), al1 }) })
    )
