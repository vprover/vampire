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

TEST_FUN(index_shared) {
  Problem p;
  Options o;
  o.resolveAwayAutoValues(p);
  Test::MockedSaturationAlgorithm alg(p, o);

  Indexing::IndexManager imgr(alg);
  auto index = imgr.request<TestIndex, /*isGenerating=*/true>();
  auto index2 = imgr.request<TestIndex, /*isGenerating=*/true>();
  ASS_EQ(index, index2);

  typedef TestIndex TestIndexDef;
  auto index3 = imgr.request<TestIndexDef, /*isGenerating=*/true>();
  ASS_EQ(index, index3);

  using TestIndexUsing = TestIndex;
  auto index4 = imgr.request<TestIndexDef, /*isGenerating=*/true>();
  ASS_EQ(index, index4);

  imgr.release<TestIndex, /*isGenerating=*/true>();
  imgr.release<TestIndex, /*isGenerating=*/true>();
  imgr.release<TestIndexDef, /*isGenerating=*/true>();
  imgr.release<TestIndexUsing, /*isGenerating=*/true>();
}

TEST_FUN(index_refcounted) {
  Problem p;
  Options o;
  o.resolveAwayAutoValues(p);
  Test::MockedSaturationAlgorithm alg(p, o);

  Indexing::IndexManager imgr(alg);

  // TODO for whatever reason I cannot put res1 into ASS()
  auto res1 = imgr.contains<TestIndex, /*isGenerating=*/true>();
  ASS(!res1);

  imgr.request<TestIndex, /*isGenerating=*/true>();
  auto res2 = imgr.contains<TestIndex, /*isGenerating=*/true>();
  ASS(res2);

  imgr.request<TestIndex, /*isGenerating=*/true>();
  auto res3 = imgr.contains<TestIndex, /*isGenerating=*/true>();
  ASS(res3);

  imgr.release<TestIndex, /*isGenerating=*/true>();
  auto res4 = imgr.contains<TestIndex, /*isGenerating=*/true>();
  ASS(res4);

  imgr.release<TestIndex, /*isGenerating=*/true>();
  auto res5 = imgr.contains<TestIndex, /*isGenerating=*/true>();
  ASS(!res5);
}

TEST_FUN(index_not_shared) {
  Problem p;
  Options o;
  o.resolveAwayAutoValues(p);
  Test::MockedSaturationAlgorithm alg(p, o);

  Indexing::IndexManager imgr(alg);
  auto index = imgr.request<TestIndex, /*isGenerating=*/true>();
  auto index2 = imgr.request<TestIndex, /*isGenerating=*/false>();
  ASS_NEQ(index, index2);

  imgr.release<TestIndex, /*isGenerating=*/true>();
  imgr.release<TestIndex, /*isGenerating=*/false>();
}

TEST_FUN(clause_appears_in_generating_index) {
  Problem p;
  Options o;
  o.resolveAwayAutoValues(p);
  Test::MockedSaturationAlgorithm alg(p, o);

  Indexing::IndexManager imgr(alg);
  auto gindex = imgr.request<TestIndex, /*isGenerating=*/true>();
  auto sindex = imgr.request<TestIndex, /*isGenerating=*/false>();

  auto cl = clause({});
  auto cl2 = clause({});
  cl->setStore(Clause::ACTIVE);
  alg.getGeneratingClauseContainer()->add(cl);
  ASS(gindex->cls.contains(cl));
  ASS(!gindex->cls.contains(cl2));
  ASS(!sindex->cls.contains(cl));
  ASS(!sindex->cls.contains(cl2));

  imgr.release<TestIndex, /*isGenerating=*/true>();
  imgr.release<TestIndex, /*isGenerating=*/false>();
}

TEST_FUN(clause_appears_in_simplifying_index) {
  Problem p;
  Options o;
  o.resolveAwayAutoValues(p);
  Test::MockedSaturationAlgorithm alg(p, o);

  Indexing::IndexManager imgr(alg);
  auto gindex = imgr.request<TestIndex, /*isGenerating=*/true>();
  auto sindex = imgr.request<TestIndex, /*isGenerating=*/false>();

  auto cl = clause({});
  auto cl2 = clause({});
  alg.getSimplifyingClauseContainer()->add(cl);
  ASS(!gindex->cls.contains(cl));
  ASS(!gindex->cls.contains(cl2));
  ASS(sindex->cls.contains(cl));
  ASS(!sindex->cls.contains(cl2));

  imgr.release<TestIndex, /*isGenerating=*/true>();
  imgr.release<TestIndex, /*isGenerating=*/false>();
}
