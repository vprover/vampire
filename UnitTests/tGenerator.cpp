/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Lib/Generator.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Stack.hpp"
#include "Lib/VirtualIterator.hpp"
#include "Test/UnitTesting.hpp"

using namespace Lib;

static Generator<int> countTo(int n)
{
  for (int i = 0; i < n; i++)
    co_yield i;
}

static Generator<int> nestedLoops()
{
  for (int i = 0; i < 3; i++)
    for (int j = 0; j < 2; j++)
      co_yield 10 * i + j;
}

static Stack<int> drain(Generator<int> gen)
{
  Stack<int> out;
  while (gen.hasNext())
    out.push(gen.next());
  return out;
}

TEST_FUN(empty)
{
  auto gen = countTo(0);
  ASS(!gen.hasNext())
  // asking again is still fine
  ASS(!gen.hasNext())
}

TEST_FUN(single_element)
{
  ASS_EQ(drain(countTo(1)), Stack<int>({0}))
}

TEST_FUN(nested_loops)
{
  ASS_EQ(drain(nestedLoops()), Stack<int>({0, 1, 10, 11, 20, 21}))
}

/** creating a Generator must not run any of its body: the first hasNext() does */
TEST_FUN(lazy_start)
{
  bool started = false;
  auto gen = [](bool& started) -> Generator<int> {
    started = true;
    co_yield 1;
  }(started);

  ASS(!started)
  ASS(gen.hasNext())
  ASS(started)
  ASS_EQ(gen.next(), 1)
}

/** hasNext() must be idempotent: calling it twice must not consume an element */
TEST_FUN(has_next_idempotent)
{
  auto gen = countTo(3);
  Stack<int> out;
  while (gen.hasNext()) {
    ASS(gen.hasNext())
    ASS(gen.hasNext())
    out.push(gen.next());
  }
  ASS_EQ(out, Stack<int>({0, 1, 2}))
}

/** an exception thrown by the body surfaces on the consumer's stack, out of hasNext() */
TEST_FUN(exception_propagates)
{
  auto gen = []() -> Generator<int> {
    co_yield 7;
    throw 42;
  }();

  ASS(gen.hasNext())
  ASS_EQ(gen.next(), 7)

  bool caught = false;
  try {
    gen.hasNext();
  } catch (int thrown) {
    caught = thrown == 42;
  }
  ASS(caught)
}

/** RAII probe: records in a counter when it is destroyed */
struct DtorProbe {
  int* destroyed;
  DtorProbe(int* destroyed) : destroyed(destroyed) {}
  DtorProbe(DtorProbe const&) = delete;
  ~DtorProbe() { (*destroyed)++; }
};

/**
 * Destroying a *partially consumed* Generator must run the destructors of everything the
 * suspended body still holds. This is what releases (and backtracks) the substitution-tree
 * iterators an inference rule was walking, and LookaheadLiteralSelector::pickTheBest relies
 * on it: it abandons partially consumed iterators by design.
 */
TEST_FUN(destroy_while_suspended_runs_destructors)
{
  int destroyed = 0;
  {
    auto gen = [](int* destroyed) -> Generator<int> {
      DtorProbe probe(destroyed);
      for (int i = 0; i < 100; i++)
        co_yield i;
    }(&destroyed);

    ASS(gen.hasNext())
    ASS_EQ(gen.next(), 0)
    ASS(gen.hasNext())
    ASS_EQ(gen.next(), 1)
    ASS_EQ(destroyed, 0)
    // gen goes out of scope here, still suspended in the middle of the loop
  }
  ASS_EQ(destroyed, 1)
}

/** move-assigning over a partially consumed Generator destroys it just as ~Generator does */
TEST_FUN(move_assign_destroys_old)
{
  int destroyed = 0;
  auto make = [](int* destroyed) -> Generator<int> {
    DtorProbe probe(destroyed);
    for (int i = 0; i < 100; i++)
      co_yield i;
  };

  auto gen = make(&destroyed);
  ASS(gen.hasNext())
  ASS_EQ(gen.next(), 0)
  ASS_EQ(destroyed, 0)

  gen = countTo(2);
  ASS_EQ(destroyed, 1)
  ASS(gen.hasNext())
  ASS_EQ(gen.next(), 0)
}

/**
 * The LookaheadLiteralSelector::pickTheBest access pattern in miniature: several
 * generators alive at once, advanced round-robin one element each until one runs dry,
 * then all abandoned.
 */
TEST_FUN(round_robin_then_abandon)
{
  int destroyed = 0;
  auto make = [](int* destroyed, int n) -> Generator<int> {
    DtorProbe probe(destroyed);
    for (int i = 0; i < n; i++)
      co_yield i;
  };

  Stack<Generator<int>> gens;
  gens.push(make(&destroyed, 5));
  gens.push(make(&destroyed, 2));
  gens.push(make(&destroyed, 7));

  unsigned exhausted = 0;
  unsigned rounds = 0;
  while (exhausted == 0) {
    rounds++;
    for (auto& gen : gens) {
      if (gen.hasNext())
        gen.next();
      else
        exhausted++;
    }
  }
  // the shortest generator yields 2 elements, so it runs dry in the third round
  ASS_EQ(rounds, 3u)
  ASS_EQ(exhausted, 1u)

  gens.reset();
  ASS_EQ(destroyed, 3)
}

/** a Generator boxed into a VirtualIterator behaves identically */
TEST_FUN(pvi_roundtrip)
{
  VirtualIterator<int> it = pvi(nestedLoops());
  Stack<int> out;
  while (it.hasNext())
    out.push(it.next());
  ASS_EQ(out, Stack<int>({0, 1, 10, 11, 20, 21}))
}

/** ...and composes with the usual combinators */
TEST_FUN(composes_with_iter_traits)
{
  auto out = iterTraits(countTo(5))
    .filter([](int x) { return x % 2 == 0; })
    .map([](int x) { return x * 10; })
    .collect<Stack>();
  ASS_EQ(out, Stack<int>({0, 20, 40}))
}
