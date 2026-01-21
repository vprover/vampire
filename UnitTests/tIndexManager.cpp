/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Indexing/IndexManager.hpp"
#include "Test/MockedSaturationAlgorithm.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Test/UnitTesting.hpp"

struct TestIndex : public Index
{
  TestIndex(SaturationAlgorithm&) {}

  void handleClause(Clause* c, bool adding) override {
    if (adding) {
      ALWAYS(cls.insert(c));
    } else {
      ALWAYS(cls.remove(c));
    }
  }
  DHSet<Clause*> cls;
};

GEN_INDEX_IMPL(TestIndex)
SIMP_INDEX_IMPL(TestIndex)

TEST_FUN(index_shared) {
  Problem p;
  Options o;
  o.resolveAwayAutoValues(p);
  Test::MockedSaturationAlgorithm alg(p, o);

  Indexing::IndexManager imgr(alg);
  auto index = imgr.get<TestIndex, /*isGenerating=*/true>();
  auto index2 = imgr.get<TestIndex, /*isGenerating=*/true>();
  ASS(index);
  ASS_EQ(index, index2);

  typedef TestIndex TestIndexDef;
  auto index3 = imgr.get<TestIndexDef, /*isGenerating=*/true>();
  ASS_EQ(index, index3);

  auto index4 = imgr.get<TestIndexDef, /*isGenerating=*/true>();
  ASS_EQ(index, index4);
}

TEST_FUN(index_not_shared) {
  Problem p;
  Options o;
  o.resolveAwayAutoValues(p);
  Test::MockedSaturationAlgorithm alg(p, o);

  Indexing::IndexManager imgr(alg);
  auto index = imgr.get<TestIndex, /*isGenerating=*/true>();
  auto index2 = imgr.get<TestIndex, /*isGenerating=*/false>();
  ASS(index);
  ASS_NEQ(index, index2);
}

TEST_FUN(clause_appears_in_generating_index) {
  Problem p;
  Options o;
  o.resolveAwayAutoValues(p);
  Test::MockedSaturationAlgorithm alg(p, o);

  Indexing::IndexManager imgr(alg);
  auto gindex = imgr.get<TestIndex, /*isGenerating=*/true>();
  auto sindex = imgr.get<TestIndex, /*isGenerating=*/false>();

  auto cl = clause({});
  auto cl2 = clause({});
  cl->setStore(Clause::ACTIVE);
  alg.getGeneratingClauseContainer()->add(cl);
  ASS(gindex->cls.contains(cl));
  ASS(!gindex->cls.contains(cl2));
  ASS(!sindex->cls.contains(cl));
  ASS(!sindex->cls.contains(cl2));
}

TEST_FUN(clause_appears_in_simplifying_index) {
  Problem p;
  Options o;
  o.resolveAwayAutoValues(p);
  Test::MockedSaturationAlgorithm alg(p, o);

  Indexing::IndexManager imgr(alg);
  auto gindex = imgr.get<TestIndex, /*isGenerating=*/true>();
  auto sindex = imgr.get<TestIndex, /*isGenerating=*/false>();

  auto cl = clause({});
  auto cl2 = clause({});
  alg.getSimplifyingClauseContainer()->add(cl);
  ASS(!gindex->cls.contains(cl));
  ASS(!gindex->cls.contains(cl2));
  ASS(sindex->cls.contains(cl));
  ASS(!sindex->cls.contains(cl2));
}
