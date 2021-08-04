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
#include "Shell/InductionSchemeGenerator.hpp"
#include "Inferences/GeneralInduction.hpp"

using namespace Shell;
using namespace Inferences;

void check_bits(Occurrences occ, unsigned c, unsigned m) {
  while (m > 0) {
    m >>= 1;
    ASS_EQ(occ.pop_last(), c & 1);
    c >>= 1;
  }
}

TEST_FUN(Occurrences1) {
  Occurrences occ(1);
  occ.add(0);
  occ.add(1);
  occ.add(1);
  occ.add(0);
  occ.add(0);
  occ.finalize();
  const unsigned bits = 6;
  ASS_EQ(occ.num_bits(), bits);
  ASS_EQ(occ.num_set_bits(), 3);
  check_bits(occ, 0b001101, (1 << bits));
  ASS(occ.next());
  check_bits(occ, 0b001111, (1 << bits));
  ASS(occ.next());
  check_bits(occ, 0b011101, (1 << bits));
  ASS(occ.next());
  check_bits(occ, 0b011111, (1 << bits));
  ASS(occ.next());
  check_bits(occ, 0b101101, (1 << bits));
  ASS(occ.next());
  check_bits(occ, 0b101111, (1 << bits));
  ASS(occ.next());
  check_bits(occ, 0b111101, (1 << bits));
  ASS(occ.next());
  check_bits(occ, 0b111111, (1 << bits));
  ASS(!occ.next());
}

TEST_FUN(OccurrenceMap1) {
  Literal l1, l2;
  Term t1, t2;
  OccurrenceMap occMap;
  occMap.add(&l1, &t1, 1);
  occMap.add(&l1, &t1, 1);
  occMap.add(&l1, &t1, 0);
  occMap.add(&l1, &t1, 0);

  occMap.add(&l2, &t2, 0);
  occMap.add(&l2, &t2, 1);
  occMap.add(&l2, &t2, 0);
  occMap.add(&l2, &t2, 1);

  occMap.finalize();

  auto check_next = [&l1, &l2, &t1, &t2](unsigned b1, unsigned b2, IteratorCore<OccurrenceMap>& occ) {
    auto ng = occ.next();
    check_bits(ng._m.find(make_pair(&l1, &t1))->second, b1, (1 << 4));
    check_bits(ng._m.find(make_pair(&l2, &t2))->second, b2, (1 << 4));
  };

  NoGeneralizationIterator ngit(occMap);
  check_next(0b1111, 0b1111, ngit);
  ASS(!ngit.hasNext());

  GeneralizationIterator git1(occMap, false, false);
  check_next(0b0011, 0b1010, git1);
  check_next(0b0111, 0b1010, git1);
  check_next(0b1011, 0b1010, git1);
  check_next(0b1111, 0b1010, git1);
  check_next(0b0011, 0b1011, git1);
  check_next(0b0111, 0b1011, git1);
  check_next(0b1011, 0b1011, git1);
  check_next(0b1111, 0b1011, git1);
  check_next(0b0011, 0b1110, git1);
  check_next(0b0111, 0b1110, git1);
  check_next(0b1011, 0b1110, git1);
  check_next(0b1111, 0b1110, git1);
  check_next(0b0011, 0b1111, git1);
  check_next(0b0111, 0b1111, git1);
  check_next(0b1011, 0b1111, git1);
  check_next(0b1111, 0b1111, git1);
  ASS(!git1.hasNext());

  GeneralizationIterator git2(occMap, true, false);
  check_next(0b0011, 0b1010, git2);
  check_next(0b1111, 0b1010, git2);
  check_next(0b0011, 0b1111, git2);
  check_next(0b1111, 0b1111, git2);
  ASS(!git2.hasNext());
}
