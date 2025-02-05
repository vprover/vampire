#include <climits>

#include "Test/UnitTesting.hpp"

#include "Benchmarking/BenchUtils.hpp"


TEST_FUN(EmptyInstruction)
{
  bench::InstrCounter c0;
  bench::InstrCounter c1;

  c0.start();
  c0.stop();
  ASS_EQ(c0.getTotalInstrCount(), 0);
}

TEST_FUN(NonEmptyInstruction)
{
  bench::InstrCounter c0;
  bench::InstrCounter c1;

  c0.start();
  ASS_EQ(c0.getTotalInstrCount(), 0);
  c0.stop();
  ASS_NEQ(c0.getTotalInstrCount(), 0);
}

TEST_FUN(EmbeddedEmptyInstruction)
{
  bench::InstrCounter c0;
  bench::InstrCounter c1;

  c1.start();
  c0.start();
  c0.stop();
  c1.stop();
  ASS_EQ(c0.getTotalInstrCount(), 0);
  ASS_EQ(c1.getTotalInstrCount(), 0);
}

TEST_FUN(Embedded3EmptyInstruction)
{
  bench::InstrCounter c0;
  bench::InstrCounter c1;
  bench::InstrCounter c2;

  c2.start();
  c1.start();
  c0.start();
  c0.stop();
  c1.stop();
  c2.stop();

  ASS_EQ(c0.getTotalInstrCount(), 0);
  ASS_EQ(c1.getTotalInstrCount(), 0);
  ASS_EQ(c2.getTotalInstrCount(), 0);
}

// We use volatile such that the expression is not optimized away
static volatile unsigned uselessVariable = 0;

TEST_FUN(EmbeddedInstruction)
{
  bench::InstrCounter c0;
  bench::InstrCounter c1;

  c0.start();
  c1.start();
  // Do somehting.
  ASS_EQ(c0.getTotalInstrCount(), 0);
  c1.stop();
  c0.stop();
  ASS_EQ(c0.getTotalInstrCount(), c1.getTotalInstrCount());
  ASS_NEQ(c0.getTotalInstrCount(), 0);
  ASS_NEQ(c1.getTotalInstrCount(), 0);
}

TEST_FUN(Embedded3Instruction)
{
  bench::InstrCounter c0;
  bench::InstrCounter c1;
  bench::InstrCounter c2;

  c0.start();
  c1.start();
  c2.start();
  // Do somehting.
  ASS_EQ(c0.getTotalInstrCount(), 0);
  c2.stop();
  c1.stop();
  c0.stop();
  ASS_EQ(c0.getTotalInstrCount(), c1.getTotalInstrCount());
  ASS_EQ(c0.getTotalInstrCount(), c2.getTotalInstrCount());
  ASS_NEQ(c0.getTotalInstrCount(), 0);
  ASS_NEQ(c1.getTotalInstrCount(), 0);
  ASS_NEQ(c2.getTotalInstrCount(), 0);
}

TEST_FUN(InvisibleInsideCounter)
{
  bench::InstrCounter c0;
  bench::InstrCounter c1;

  c0.start();
  c1.start();
  // Do somehting.
  ASS_EQ(c0.getTotalInstrCount(), 0);
  c1.stop();
  c0.stop();

  long long firstCount = c0.getTotalInstrCount();

  // we remove the inner counter, and should get the same result
  c0.reset();
  c0.start();
  // Do somehting.
  ASS_EQ(c0.getTotalInstrCount(), 0);
  c0.stop();

  ASS_EQ(c0.getTotalInstrCount(), firstCount);
}
