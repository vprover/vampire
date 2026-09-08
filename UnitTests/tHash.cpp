/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include <cstdint>
#include <string>
#include <tuple>
#include <utility>

#include "Lib/Hash.hpp"
#include "Lib/Stack.hpp"
#include "Test/UnitTesting.hpp"

using namespace Lib;

// FNV-1a 32-bit reference vectors, http://www.isthe.com/chongo/tech/comp/fnv/
TEST_FUN(fnvReferenceVectors)
{
  ASS_EQ(FnvHash::hashNulTerminated(""), 0x811c9dc5u);
  ASS_EQ(FnvHash::hashNulTerminated("a"), 0xe40c292cu);
  ASS_EQ(FnvHash::hashNulTerminated("foobar"), 0xbf9cf968u);
  ASS_EQ(FnvHash::hash(std::string("foobar")), 0xbf9cf968u);
}

enum TestColour { RED = 5, GREEN = 17 };

enum class TestNarrowColour : std::uint8_t { BLUE = 3 };

// the named functors compute exactly what DefaultHash/DefaultHash2 resolve to;
// keeps hash values pinned while call sites move to the named functors
TEST_FUN(namedFunctorsMatchDefaultHash)
{
  unsigned u = 12345;
  int i = -7;
  double d = 3.14;
  ASS_EQ(FnvHash::hash(u), DefaultHash::hash(u));
  ASS_EQ(FnvHash::hash(i), DefaultHash::hash(i));
  ASS_EQ(FnvHash::hash(d), DefaultHash::hash(d));
  ASS_EQ(FnvHash::hash(GREEN), DefaultHash::hash(GREEN));
  ASS_EQ(IdentityHash::hash(u), DefaultHash2::hash(u));
  ASS_EQ(IdentityHash::hash(i), DefaultHash2::hash(i));
  ASS_EQ(IdentityHash::hash(GREEN), DefaultHash2::hash(GREEN));

  int* p = &i;
  ASS_EQ(FnvHash::hash(p), DefaultHash::hash(p));
  ASS_EQ(PtrIdentityHash::hash(p), DefaultHash2::hash(p));

  std::string s("hello");
  ASS_EQ(FnvHash::hash(s), DefaultHash::hash(s));
  ASS_EQ(LengthHash::hash(s), DefaultHash2::hash(s));

  Kernel::Unit* noUnit = nullptr;
  ASS_EQ(UnitHash::hash(noUnit), DefaultHash::hash(noUnit));
  ASS_EQ(UnitHash::hash(noUnit), FnvHash::hash(0u));
  ASS_EQ(UnitNumberHash::hash(noUnit), DefaultHash2::hash(noUnit));
  ASS_EQ(UnitNumberHash::hash(noUnit), 0u);

  auto pr = std::make_pair(u, s);
  using PrimaryPairHash = PairHash<FnvHash, FnvHash>;
  using SecondaryPairHash = PairHash<IdentityHash, LengthHash>;
  ASS_EQ(PrimaryPairHash::hash(pr), DefaultHash::hash(pr));
  ASS_EQ(SecondaryPairHash::hash(pr), DefaultHash2::hash(pr));

  // the elements of a tuple need not agree on a functor: here the pointer takes
  // PtrIdentityHash, the unsigned IdentityHash and the string LengthHash
  auto tp = std::make_tuple(p, u, s);
  using PrimaryTupleHash = TupleHash<FnvHash, FnvHash, FnvHash>;
  using SecondaryTupleHash = TupleHash<PtrIdentityHash, IdentityHash, LengthHash>;
  ASS_EQ(PrimaryTupleHash::hash(tp), DefaultHash::hash(tp));
  ASS_EQ(SecondaryTupleHash::hash(tp), DefaultHash2::hash(tp));

  // the shape PartialOrdering caches on, which also pins how combine() nests
  // for four elements
  auto po = std::make_tuple(p, size_t(1), size_t(2), TestNarrowColour::BLUE);
  using PrimaryPoHash = TupleHash<FnvHash, FnvHash, FnvHash, FnvHash>;
  using SecondaryPoHash = TupleHash<PtrIdentityHash, IdentityHash, IdentityHash, IdentityHash>;
  ASS_EQ(PrimaryPoHash::hash(po), DefaultHash::hash(po));
  ASS_EQ(SecondaryPoHash::hash(po), DefaultHash2::hash(po));

  // the nested shape InductionFormulaIndex keys on: DefaultHash walks the stacks
  // element by element, DefaultHash2 takes the outer stack's length
  Stack<Stack<int*>> outer;
  outer.push(Stack<int*>());
  outer.top().push(p);
  auto nested = std::make_pair(outer, std::make_pair(p, p));
  using PrimaryNestedHash = PairHash<StackHash<StackHash<FnvHash>>, PairHash<FnvHash, FnvHash>>;
  using SecondaryNestedHash = PairHash<LengthHash, PairHash<PtrIdentityHash, PtrIdentityHash>>;
  ASS_EQ(PrimaryNestedHash::hash(nested), DefaultHash::hash(nested));
  ASS_EQ(SecondaryNestedHash::hash(nested), DefaultHash2::hash(nested));
}
