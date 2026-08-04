/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include <set>

#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/FormulaVarIterator.hpp"
#include "Kernel/Inference.hpp"

#include "Shell/Miniscoping.hpp"

using namespace Kernel;
using namespace Shell;

static Formula* lit(Literal* l)
{
  return new AtomicFormula(l);
}

static Formula* junction(Connective con, std::initializer_list<Formula*> fs)
{
  FormulaList::FIFO args;
  for (Formula* f : fs) {
    args.pushBack(f);
  }
  return new JunctionFormula(con, args.list());
}

static Formula* conj(std::initializer_list<Formula*> fs) { return junction(AND, fs); }
static Formula* disj(std::initializer_list<Formula*> fs) { return junction(OR, fs); }

static Formula* quant(Connective q, std::initializer_list<unsigned> vars, TermList sort, Formula* g)
{
  VSList::FIFO vs;
  for (unsigned v : vars) {
    vs.pushBack(VarSort(v, sort));
  }
  return new QuantifiedFormula(q, vs.list(), g);
}

/** every variable is bound at most once */
static void checkRectified(Formula* f)
{
  VSList* bound = f->boundVariables();
  std::set<unsigned> seen;
  VSList::Iterator it(bound);
  while (it.hasNext()) {
    unsigned v = it.next().first;
    ASS_REP(seen.insert(v).second, f->toString());
  }
  VSList::destroy(bound);
}

static std::set<unsigned> freeVarSet(Formula* f)
{
  std::set<unsigned> res;
  FormulaVarIterator fvi(f);
  while (fvi.hasNext()) {
    res.insert(fvi.next());
  }
  return res;
}

static void checkResult(Formula* in, Formula* expected,
                        Miniscoping::Mode mode = Miniscoping::Mode::ON)
{
  Formula* out = Miniscoping::miniscope(in, mode);
  ASS_EQ(out->toString(), expected->toString());
  ASS(freeVarSet(in) == freeVarSet(out));
  checkRectified(out);
}

#define MY_SYNTAX_SUGAR \
  DECL_SORT(srt)        \
  DECL_VAR(x, 0)        \
  DECL_VAR(y, 1)        \
  DECL_VAR(z, 2)        \
  DECL_VAR(w, 3)        \
  DECL_CONST(a, srt)    \
  DECL_PRED(p, {srt})   \
  DECL_PRED(q, {srt})   \
  DECL_PRED(r, {srt})   \
  DECL_PRED(p2, {srt, srt})

TEST_FUN(forall_over_and)
{
  MY_SYNTAX_SUGAR
  // ![X0]: (p(X0) & q(X0)) ---> ![X0]: p(X0) & ![X1]: q(X1)
  checkResult(quant(FORALL, {0}, srt, conj({lit(p(x)), lit(q(x))})),
              conj({quant(FORALL, {0}, srt, lit(p(x))),
                    quant(FORALL, {1}, srt, lit(q(y)))}));
}

TEST_FUN(exists_over_or)
{
  MY_SYNTAX_SUGAR
  // ?[X0]: (p(X0) | q(X0)) ---> ?[X0]: p(X0) | ?[X1]: q(X1)
  checkResult(quant(EXISTS, {0}, srt, disj({lit(p(x)), lit(q(x))})),
              disj({quant(EXISTS, {0}, srt, lit(p(x))),
                    quant(EXISTS, {1}, srt, lit(q(y)))}));
}

TEST_FUN(forall_or_partition)
{
  MY_SYNTAX_SUGAR
  // ![X0]: (p(X0) | r(a) | q(X0)) ---> ![X0]: (p(X0) | q(X0)) | r(a)
  checkResult(quant(FORALL, {0}, srt, disj({lit(p(x)), lit(r(a)), lit(q(x))})),
              disj({quant(FORALL, {0}, srt, disj({lit(p(x)), lit(q(x))})),
                    lit(r(a))}));
}

TEST_FUN(exists_and_partition_single)
{
  MY_SYNTAX_SUGAR
  // ?[X0]: (p(X0) & r(a)) ---> ?[X0]: p(X0) & r(a)
  checkResult(quant(EXISTS, {0}, srt, conj({lit(p(x)), lit(r(a))})),
              conj({quant(EXISTS, {0}, srt, lit(p(x))), lit(r(a))}));
}

TEST_FUN(dummy_drop)
{
  MY_SYNTAX_SUGAR
  // ![X0]: r(a) ---> r(a), sharing the body
  Formula* body = lit(r(a));
  ASS_EQ(Miniscoping::miniscope(quant(FORALL, {0}, srt, body)), body);

  // ![X0,X1]: p(X0) ---> ![X0]: p(X0)
  checkResult(quant(FORALL, {0,1}, srt, lit(p(x))),
              quant(FORALL, {0}, srt, lit(p(x))));
}

TEST_FUN(block_split_no_rename)
{
  MY_SYNTAX_SUGAR
  // ![X0,X1]: (p(X0) & q(X1)) ---> ![X0]: p(X0) & ![X1]: q(X1), no fresh variables
  checkResult(quant(FORALL, {0,1}, srt, conj({lit(p(x)), lit(q(y))})),
              conj({quant(FORALL, {0}, srt, lit(p(x))),
                    quant(FORALL, {1}, srt, lit(q(y)))}));
}

TEST_FUN(bottom_up_one_pass)
{
  MY_SYNTAX_SUGAR
  // ![X0]: ?[X1]: (p(X1) | q(X0)) ---> ?[X1]: p(X1) | ![X0]: q(X0)
  // (the inner block must split out first for the outer one to move)
  checkResult(quant(FORALL, {0}, srt, quant(EXISTS, {1}, srt, disj({lit(p(y)), lit(q(x))}))),
              disj({quant(EXISTS, {1}, srt, lit(p(y))),
                    quant(FORALL, {0}, srt, lit(q(x)))}));
}

TEST_FUN(quantifier_swap)
{
  MY_SYNTAX_SUGAR
  // ![X0,X1]: (p2(X0,X1) | q(X1)) ---> ![X1]: (![X0]: p2(X0,X1) | q(X1))
  checkResult(quant(FORALL, {0,1}, srt, disj({lit(p2(x,y)), lit(q(y))})),
              quant(FORALL, {1}, srt,
                    disj({quant(FORALL, {0}, srt, lit(p2(x,y))), lit(q(y))})));
}

TEST_FUN(no_change_sharing)
{
  MY_SYNTAX_SUGAR
  // ![X0]: (p(X0) | q(X0)) is already miniscoped: same formula and unit returned
  Formula* f = quant(FORALL, {0}, srt, disj({lit(p(x)), lit(q(x))}));
  ASS_EQ(Miniscoping::miniscope(f), f);

  FormulaUnit* u = new FormulaUnit(f, FromInput(UnitInputType::AXIOM));
  ASS_EQ(Miniscoping::miniscope(u), u);
}

TEST_FUN(unit_and_inference)
{
  MY_SYNTAX_SUGAR
  Formula* f = quant(EXISTS, {0}, srt, conj({lit(p(x)), lit(r(a))}));
  FormulaUnit* u = new FormulaUnit(f, FromInput(UnitInputType::AXIOM));

  FormulaUnit* res = Miniscoping::miniscope(u);
  ASS_NEQ(res, u);
  ASS(res->inference().rule() == InferenceRule::MINISCOPE);
  ASS_EQ(ruleName(res->inference().rule()), "miniscoping");

  Inference::Iterator it = res->inference().iterator();
  ASS(res->inference().hasNext(it));
  ASS_EQ(res->inference().next(it), u);
  ASS(!res->inference().hasNext(it));

  ASS(freeVarSet(f) == freeVarSet(res->formula()));
  checkRectified(res->formula());
}

TEST_FUN(no_esplit_partitions_instead)
{
  MY_SYNTAX_SUGAR
  // ?[X0]: (p(X0) | q(X0) | r(a)) ---> ?[X0]: (p(X0) | q(X0)) | r(a)
  // (under no_esplit the binder is not duplicated; the x-free junct still leaves)
  checkResult(quant(EXISTS, {0}, srt, disj({lit(p(x)), lit(q(x)), lit(r(a))})),
              disj({quant(EXISTS, {0}, srt, disj({lit(p(x)), lit(q(x))})),
                    lit(r(a))}),
              Miniscoping::Mode::NO_ESPLIT);
}

TEST_FUN(no_esplit_stuck_sharing)
{
  MY_SYNTAX_SUGAR
  // ?[X0]: (p(X0) | q(X0)) cannot move without splitting: same formula returned
  Formula* f = quant(EXISTS, {0}, srt, disj({lit(p(x)), lit(q(x))}));
  ASS_EQ(Miniscoping::miniscope(f, Miniscoping::Mode::NO_ESPLIT), f);
}

TEST_FUN(no_esplit_still_splits_forall)
{
  MY_SYNTAX_SUGAR
  // universal distribution is skolem-neutral and stays on under no_esplit ...
  Formula* in = quant(FORALL, {0}, srt, conj({lit(p(x)), lit(q(x))}));
  checkResult(in,
              conj({quant(FORALL, {0}, srt, lit(p(x))),
                    quant(FORALL, {1}, srt, lit(q(y)))}),
              Miniscoping::Mode::NO_ESPLIT);
  // ... but is off under no_split (the formula reproduces itself)
  ASS_EQ(Miniscoping::miniscope(in, Miniscoping::Mode::NO_SPLIT), in);
}

TEST_FUN(no_esplit_usplit_enables_dep_shedding)
{
  MY_SYNTAX_SUGAR
  // ![X0]: ?[X1]: ![X2]: (p2(X2,X1) & p2(X2,X0))
  //   ---> ?[X1]: ![X2]: p2(X2,X1) & ![X0,X3]: p2(X3,X0)
  // (only the universal split of X2 lets X1's block shed X0 from below itself,
  //  making X1's skolem a constant instead of a function of X0)
  checkResult(quant(FORALL, {0}, srt,
                    quant(EXISTS, {1}, srt,
                          quant(FORALL, {2}, srt, conj({lit(p2(z,y)), lit(p2(z,x))})))),
              conj({quant(EXISTS, {1}, srt, quant(FORALL, {2}, srt, lit(p2(z,y)))),
                    quant(FORALL, {0,3}, srt, lit(p2(w,x)))}),
              Miniscoping::Mode::NO_ESPLIT);
}

TEST_FUN(rename_into_pushed_copy)
{
  MY_SYNTAX_SUGAR
  // ![X0,X1]: (p2(X0,X1) & p2(X0,X1))
  //   ---> ![X0,X1]: p2(X0,X1) & ![X3,X2]: p2(X3,X2)
  // (X1 distributes first, renaming its second copy to X2; then X0
  //  pushes into both conjuncts, entering the fresh copy renamed to X3)
  checkResult(quant(FORALL, {0,1}, srt, conj({lit(p2(x,y)), lit(p2(x,y))})),
              conj({quant(FORALL, {0,1}, srt, lit(p2(x,y))),
                    quant(FORALL, {3,2}, srt, lit(p2(w,z)))}));
}

TEST_FUN(deep_chain_descent)
{
  MY_SYNTAX_SUGAR
  // the quantifier sinks through a deep alternating &/| chain
  // all the way down to the single occurrence of its variable
  Formula* in = lit(p(x));
  Formula* expected = quant(FORALL, {0}, srt, lit(p(x)));
  for (unsigned i = 0; i < 50; i++) {
    if (i % 2 == 0) {
      in = disj({lit(r(a)), in});
      expected = disj({lit(r(a)), expected});
    } else {
      in = conj({lit(q(a)), in});
      expected = conj({lit(q(a)), expected});
    }
  }
  checkResult(quant(FORALL, {0}, srt, in), expected);
}

TEST_FUN(sort_preservation)
{
  MY_SYNTAX_SUGAR
  // the renamed copy of a duplicated binder keeps the original sort
  Formula* out = Miniscoping::miniscope(quant(FORALL, {0}, srt, conj({lit(p(x)), lit(q(x))})));
  ASS_EQ(out->connective(), AND);
  FormulaList::Iterator it(out->args());
  while (it.hasNext()) {
    Formula* c = it.next();
    ASS_EQ(c->connective(), FORALL);
    ASS_EQ(c->vars()->head().second, TermList(srt));
  }
}
