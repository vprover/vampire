/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include <string>
#include <utility>

#include "Lib/Hash.hpp"
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
}
