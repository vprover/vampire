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
#include "Kernel/BottomUpEvaluation.hpp"
#include "Kernel/BottomUpEvaluation/TermList.hpp"
#include "Kernel/Term.hpp"

using namespace Kernel;
using namespace Inferences;
using namespace Test;

TEST_FUN(example_01__replace_all_vars_by_term) {
  /* syntax sugar imports */
  DECL_DEFAULT_VARS
  DECL_SORT(s)
  DECL_CONST(a, s)
  DECL_FUNC(f, {s}, s)
  DECL_FUNC(g, {s,s}, s)

  /* defines how to evaluate bottom up. 
   * all variables are being replaced by a constant term in this case */
  struct Eval {
    TermList replacement;

    using Arg    = TermList;
    using Result = TermList;

    TermList operator()(TermList toEval, TermList* evaluatedChildren) {
      if (toEval.isVar()) {
        return replacement;
      } else {
        return TermList(Term::create(toEval.term(), evaluatedChildren));
      }
    }
  };


  /* test specification */
  TermList input    = g(f(x), y);
  TermList expected = g(f(a), a);

  /* actual evaluation */
  TermList result =  evaluateBottomUp(input, Eval{a});

  ASS_EQ(result, expected)
}

TEST_FUN(example_02__compute_size) {
  /* syntax sugar imports */
  DECL_DEFAULT_VARS
  DECL_SORT(s)
  DECL_FUNC(f, {s}, s)
  DECL_FUNC(g, {s,s}, s)

  /* defines how to evaluate bottom up. 
   * computes the size of the term (number of function & variable symbols) */
  struct Eval {
    using Arg    = TermList;
    using Result = unsigned;

    unsigned operator()(TermList toEval, unsigned* evaluatedChildren) {
      if (toEval.isVar()) {
        return 1;
      } else {
        // clang-tidy thought that evaluatedChildren could be nullptr and toEval.term()->arity > 0
        // it's wrong, but it's a nice thing to check
        unsigned arity = toEval.term()->arity();
        ASS(arity == 0 || evaluatedChildren);

        unsigned out = 1;
        for (unsigned i = 0; i < arity; i++) {
          out += evaluatedChildren[i];
        }
        return out;
      }
    }
  };


  /* test specification */
  TermList input    = g(f(x), f(f(x)));
  //                    ^^^^    ^^^^ size of this sub-term will only be evaluated once due to memo

  /* actual evaluation */
  Memo::Hashed<TermList, unsigned> memo{};
  auto size =  evaluateBottomUp(input, Eval{}, memo);

  ASS_EQ(size, 6)
}
