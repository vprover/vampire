/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include <bit>
#include <cstdint>
#include <string>
#include <tuple>
#include <utility>

#include "Lib/Coproduct.hpp"
#include "Lib/Hash.hpp"
#include "Lib/Perfect.hpp"
#include "Lib/Stack.hpp"
#include "Kernel/Polynomial.hpp"
#include "Test/UnitTesting.hpp"

using namespace Lib;
using namespace Kernel;

// FNV-1a 32-bit reference vectors, http://www.isthe.com/chongo/tech/comp/fnv/
TEST_FUN(fnvReferenceVectors)
{
  ASS_EQ(FnvHash::hashNulTerminated(""), 0x811c9dc5u);
  ASS_EQ(FnvHash::hashNulTerminated("a"), 0xe40c292cu);
  ASS_EQ(FnvHash::hashNulTerminated("foobar"), 0xbf9cf968u);
  ASS_EQ(FnvHash::hash(std::string("foobar")), 0xbf9cf968u);
}

enum class TestNarrowColour : std::uint8_t { BLUE = 3 };

TEST_FUN(scalarHashVectors)
{
  ASS_EQ(FnvHash::hash(TestNarrowColour::BLUE), 0x060c5eb2u);
  ASS_EQ(IdentityHash::hash(TestNarrowColour::BLUE), 3u);
  uint64_t word = 0x0123456789abcdefULL;
  // The scalar hash reads native bytes, so its value depends on byte order.
  if constexpr (std::endian::native == std::endian::little) {
    ASS_EQ(FnvHash::hash(word), 0xe39e4e75u);
  } else if constexpr (std::endian::native == std::endian::big) {
    ASS_EQ(FnvHash::hash(word), 0xf33f1185u);
  }
  ASS_EQ(IdentityHash::hash(word), 0x89abcdefu);
  ASS_EQ(IdentityHash::hash(-7), 0xfffffff9u);
  ASS_EQ(LengthHash::hash(std::string("hello")), 5u);
  ASS_EQ(PtrIdentityHash::hash(static_cast<int*>(nullptr)), 0u);
  ASS_EQ(UnitHash::hash(nullptr), FnvHash::hash(0u));
  ASS_EQ(UnitNumberHash::hash(nullptr), 0u);
}

// Values recorded before removing the implicit hashes. Byte-sized integers keep
// these composite vectors independent of native byte order and pointer width.
TEST_FUN(compositeHashVectors)
{
  auto pr = std::make_pair(uint8_t(3), std::string("hello"));
  using PrimaryPairHash = PairHash<FnvHash, FnvHash>;
  using SecondaryPairHash = PairHash<IdentityHash, LengthHash>;
  ASS_EQ(PrimaryPairHash::hash(pr), 0x747d3422u);
  ASS_EQ(SecondaryPairHash::hash(pr), 0x9e377a7du);

  auto tp = std::make_tuple(uint8_t(3), uint8_t(7), std::string("hello"));
  using PrimaryTupleHash = TupleHash<FnvHash, FnvHash, FnvHash>;
  using SecondaryTupleHash = TupleHash<IdentityHash, IdentityHash, LengthHash>;
  ASS_EQ(PrimaryTupleHash::hash(tp), 0x90399532u);
  ASS_EQ(SecondaryTupleHash::hash(tp), 0x3c6ef5f2u);

  auto four = std::make_tuple(uint8_t(3), uint8_t(7), uint8_t(11), std::string("hello"));
  using PrimaryFourHash = TupleHash<FnvHash, FnvHash, FnvHash, FnvHash>;
  using SecondaryFourHash = TupleHash<IdentityHash, IdentityHash, IdentityHash, LengthHash>;
  ASS_EQ(PrimaryFourHash::hash(four), 0xc71466bfu);
  ASS_EQ(SecondaryFourHash::hash(four), 0xdaa67278u);
  ASS_EQ(TupleHash<>::hash(std::make_tuple()), 0x9e3779bau);
  ASS_EQ(TupleHash<FnvHash>::hash(std::make_tuple(uint8_t(3))), 0x060c5eb2u);

  Stack<Stack<uint8_t>> outer;
  outer.push(Stack<uint8_t>());
  outer.top().push(3);
  auto nested = std::make_pair(outer, std::make_pair(uint8_t(7), uint8_t(11)));
  using PrimaryNestedHash = PairHash<StackHash<StackHash<FnvHash>>, PairHash<FnvHash, FnvHash>>;
  using SecondaryNestedHash = PairHash<LengthHash, PairHash<IdentityHash, IdentityHash>>;
  ASS_EQ(PrimaryNestedHash::hash(nested), 0x333be252u);
  ASS_EQ(SecondaryNestedHash::hash(nested), 0x3c6ef57au);
  ASS_EQ(StackHash<FnvHash>::hash(outer.top()), 0x8aaeecd9u);
  ASS_EQ(StackHash<FnvHash>::hash(outer.top(), 17), 0xa443dcbeu);
}

TEST_FUN(coproductHashUsesAlternativeIndex)
{
  using Value = Coproduct<uint8_t, std::string>;
  using Primary = CoproductHash<FnvHash, FnvHash>;
  using Secondary = CoproductHash<IdentityHash, LengthHash>;
  Value first(uint8_t(3));
  Value second(std::string("hello"));
  ASS_EQ(Primary::hash(first), 0xa443d86bu);
  ASS_EQ(Primary::hash(second), 0xedd6a6a5u);
  ASS_EQ(Secondary::hash(first), 0x9e3779bcu);
  ASS_EQ(Secondary::hash(second), 0x9e3779ffu);
  ASS(Primary::equals(second, Value(std::string("hello"))));
  ASS(!Primary::equals(first, second));

  // Repeated types may use different functors: dispatch must use the tag.
  using Repeated = Coproduct<uint8_t, uint8_t>;
  using Mixed = CoproductHash<FnvHash, IdentityHash>;
  auto a = Repeated::variant<0>(3);
  auto b = Repeated::variant<1>(3);
  ASS_EQ(Mixed::hash(a), 0xa443d86bu);
  ASS_EQ(Mixed::hash(b), 0x9e3779fdu);
  ASS(!Mixed::equals(a, b));
}

TEST_FUN(numericAndPolynomialHashes)
{
  // Integer truncation takes the magnitude, including for negative numbers.
  unsigned seven = FnvHash::hash(7ul);
  ASS_EQ(IntegerConstantTypeHash::hash(IntegerConstantType(-7)), seven);
  unsigned rational = HashUtils::combine(seven, FnvHash::hash(3ul));
  ASS_EQ(RationalConstantTypeHash::hash(RationalConstantType(-7, 3)), rational);
  ASS_EQ(RationalConstantTypeHash::hash(RealConstantType(RationalConstantType(-7, 3))), rational);

  Variable var(3);
  ASS_EQ(VariableHash::hash(var), FnvHash::hash(3u));
  ASS_EQ(PolyNfHash::hash(PolyNf(var)), HashUtils::combine(1u, FnvHash::hash(3u)));
  ASS(PolyNfHash::equals(PolyNf(var), PolyNf(Variable(3))));
  ASS(!PolyNfHash::equals(PolyNf(var), PolyNf(Variable(4))));

  // Interned polynomials use FNV of their ids in this hash. Their std::hash
  // specializations use the ids directly, and are still used by other caches.
  auto checkPolynomial = [](auto numeral, unsigned tag) {
    using Traits = NumTraits<decltype(numeral)>;
    auto p = perfect(Polynom<Traits>::fromNumeral(numeral));
    auto id = static_cast<unsigned>(PerfectIdComparison::hash(p));
    unsigned expected = HashUtils::combine(tag, FnvHash::hash(id));
    ASS_EQ(PerfectHash<FnvHash>::hash(p), FnvHash::hash(id));
    ASS_EQ(AnyPolyHash::hash(AnyPoly(p)), expected);
    ASS_EQ(PolyNfHash::hash(PolyNf(AnyPoly(p))), HashUtils::combine(2u, expected));
  };
  checkPolynomial(IntegerConstantType(7), 0);
  checkPolynomial(RationalConstantType(7, 3), 1);
  checkPolynomial(RealConstantType(RationalConstantType(7, 3)), 2);
}

TEST_FUN(uniqueIteratorsWithExplicitHashes)
{
  Stack<unsigned> values;
  values.pushMany(3u, 1u, 3u, 2u, 1u);
  auto checkPersistent = [](auto iter) {
    ASS_EQ(iter.next(), 2u);
    ASS_EQ(iter.next(), 1u);
    ASS_EQ(iter.next(), 3u);
    ASS(!iter.hasNext());
  };
  checkPersistent(getUniquePersistentIterator<FnvHash, IdentityHash>(values.iterFifo()));
  auto inner = values.iterFifo();
  checkPersistent(getUniquePersistentIteratorFromPtr<FnvHash, IdentityHash>(&inner));

  auto unique = iterTraits(values.iterFifo()).unique<FnvHash>();
  ASS_EQ(unique.next(), 3u);
  ASS_EQ(unique.next(), 1u);
  ASS_EQ(unique.next(), 2u);
  ASS(!unique.hasNext());
}
