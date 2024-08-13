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
#include "Kernel/Term.hpp"

using namespace Lib;
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

  /* test specification */
  TermList input    = g(f(x), y);
  TermList expected = g(f(a), a);

  /* actual evaluation */
  TermList result =  BottomUpEvaluation<TermList, TermList>()
    .function(
      /* defines how to evaluate bottom up. 
       * all variables are being replaced by a constant term in this case */
      [&](TermList toEval, TermList* evaluatedChildren) -> TermList {
        if (toEval.isVar()) {
          return a;
        } else {
          return TermList(Term::create(toEval.term(), evaluatedChildren));
        }
      })
    .apply(input);

  ASS_EQ(result, expected)
}

TEST_FUN(example_02__compute_size) {
  /* syntax sugar imports */
  DECL_DEFAULT_VARS
  DECL_SORT(s)
  DECL_FUNC(f, {s}, s)
  DECL_FUNC(g, {s,s}, s)


  /* test specification */
  TermList input    = g(f(x), f(f(x)));
  //                    ^^^^    ^^^^ size of this sub-term will only be evaluated once due to memo

  /* actual evaluation */
  Memo::Hashed<TermList, unsigned> memo{};
  auto size =  BottomUpEvaluation<TermList, unsigned>()
    .function(
        /* defines how to evaluate bottom up. 
         * computes the size of the term (number of function & variable symbols) */
        [&](TermList toEval, unsigned* evaluatedChildren) -> unsigned {
          if (toEval.isVar()) {
            return 1;
          } else {
            // clang-tidy thought that evaluatedChildren could be nullptr and toEval.term()->arity > 0
            // it's wrong, but it's a nice thing to check
            unsigned arity = toEval.term()->numTermArguments();
            ASS(arity == 0 || evaluatedChildren);

            unsigned out = 1;
            for (unsigned i = 0; i < arity; i++) {
              out += evaluatedChildren[i];
            }
            return out;
          }
        })
      .memo<decltype(memo)&>(memo)
      .apply(input);

  ASS_EQ(size, 6)
}
