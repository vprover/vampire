/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file LiteralSubstitutionTree.hpp
 * Defines class LiteralSubstitutionTree.
 */


#ifndef __LiteralSubstitutionTree__
#define __LiteralSubstitutionTree__

#include "Indexing/Index.hpp"
#include "Kernel/MismatchHandler.hpp"
#include "Lib/VirtualIterator.hpp"
#include "LiteralIndexingStructure.hpp"
#include "SubstitutionTree.hpp"

namespace Indexing {

/** A wrapper class around SubstitutionTree that makes it usable  as a LiteralIndexingStructure */
class LiteralSubstitutionTree
: public LiteralIndexingStructure
{
  using FastInstancesIterator = SubstitutionTree::FastInstancesIterator;
  using BindingMap = SubstitutionTree::BindingMap;
  using LDIterator = SubstitutionTree::LDIterator;
  using FastGeneralizationsIterator = SubstitutionTree::FastGeneralizationsIterator;
  using LeafData = SubstitutionTree::LeafData;
  using LeafIterator = SubstitutionTree::LeafIterator;
  using Leaf = SubstitutionTree::Leaf;

public:
  CLASS_NAME(LiteralSubstitutionTree);
  USE_ALLOCATOR(LiteralSubstitutionTree);

  LiteralSubstitutionTree();

  void insert(Literal* lit, Clause* cls) override { handleLiteral(lit, cls, /* insert */ true); }
  void remove(Literal* lit, Clause* cls) override { handleLiteral(lit, cls, /* insert */ false); }

  SLQueryResultIterator getAll() final override;
  void handleLiteral(Literal* lit, Clause* cls, bool insert)
  { getTree(lit, /* complementary */ false).handle(lit, SubstitutionTree::LeafData(cls, lit), insert); }

  SLQueryResultIterator getUnifications(Literal* lit, bool complementary, bool retrieveSubstitutions) final override;

  SLQueryResultIterator getGeneralizations(Literal* lit, bool complementary, bool retrieveSubstitutions) final override;
  SLQueryResultIterator getInstances(Literal* lit, bool complementary, bool retrieveSubstitutions) final override;
  SLQueryResultIterator getVariants(Literal* lit, bool complementary, bool retrieveSubstitutions) final override;

private:
  static unsigned idxToFunctor(unsigned idx) { return idx / 2; }
  static bool idxIsNegative(unsigned idx) { return idx % 2; }
  static unsigned toIdx(unsigned f, bool isNegative) { return f * 2 + isNegative; }

  template<class Iterator, class... Args>
  auto getResultIterator(Literal* lit, bool complementary, bool retrieveSubstitutions, Args... args)
  {
    CALL("LiteralSubstitutionTree::getResultIterator");

    auto iter = [=](bool reversed) 
      { return iterTraits(getTree(lit, complementary).template iterator<Iterator>(lit, retrieveSubstitutions, reversed, args...)) ; };

    auto filterResults = [=](auto it) { 
      return pvi(
          std::move(it)
          .map([](auto r) { return lQueryRes(r.data->literal, r.data->clause, std::move(r.unif)); })
          ); 
    };
    return !lit->commutative() 
      ?  filterResults(iter( /* reversed */ false))
      :  filterResults(concatIters(
          iter( /* reversed */ false),
          iter( /* reversed */ true)
        ));
  }


  auto nopostproUwa(Literal* lit, bool complementary, Options::UnificationWithAbstraction uwa)
  { return getResultIterator<SubstitutionTree::Iterator<RetrievalAlgorithms::UnificationWithAbstraction>>(lit, complementary, /* retrieveSubstitutions */ true, MismatchHandler(uwa)); }

  auto postproUwa(Literal* lit, bool complementary, Options::UnificationWithAbstraction uwa)
  { return pvi(iterTraits(getResultIterator<SubstitutionTree::Iterator<RetrievalAlgorithms::UnificationWithAbstractionWithPostprocessing>>(lit, complementary, /* retrieveSubstitutions */ true, MismatchHandler(uwa)))
    .filterMap([](LQueryRes<RetrievalAlgorithms::UnificationWithAbstractionWithPostprocessing::NotFinalized> r)
        { return r.unifier.fixedPointIteration().map([&](AbstractingUnifier* unif) { return lQueryRes(r.literal, r.clause, unif); }); })); }


public:


  VirtualIterator<LQueryRes<AbstractingUnifier*>> getUwa(Literal* lit, bool complementary, Options::UnificationWithAbstraction uwa, bool fixedPointIteration) final override
  { return fixedPointIteration ? pvi(  postproUwa(lit, complementary, uwa))
                               : pvi(nopostproUwa(lit, complementary, uwa)); }

  friend std::ostream& operator<<(std::ostream& out, LiteralSubstitutionTree const& self)
  { 
    int i = 0;
    out << "{ ";
    for (auto& t : self._trees) {
      if (!t.isEmpty()) {
        auto f = env.signature->getPredicate(idxToFunctor(i));
        if (idxIsNegative(i)) out << "~";
        out << *f << "(" << t << "), "; 
      }
      i++;
    }
    return out << "} ";
  }
  friend std::ostream& operator<<(std::ostream& out, OutputMultiline<LiteralSubstitutionTree> const& self)
  { 
    int i = 0;
    out << "{ " << endl;
    for (auto& t : self.self._trees) {
      if (!t.isEmpty()) {
        auto f = env.signature->getPredicate(idxToFunctor(i));
        OutputMultiline<LiteralSubstitutionTree>::outputIndent(out, self.indent);
        out << (idxIsNegative(i) ? "~" : " ") << *f << "(" << multiline(t, self.indent + 1) << ")" << endl; 
      }
      i++;
    }
    return out << "} ";
  }


private:
  SubstitutionTree& getTree(Literal* lit, bool complementary)
  {
    auto idx = complementary ? lit->header() : lit->complementaryHeader();
    while (idx >= _trees.size()) {
      _trees.push(SubstitutionTree());
    }
    return _trees[idx];
  }

  // static auto createSLQueryResult(SubstitutionTree::QueryResult<Option<AbstractingUnifier*>> r)
  // { return lQueryRes(r.data->literal, r.data->clause, *r.unif); }
  //
  // static auto createSLQueryResult(SubstitutionTree::QueryResult<Option<RobSubstitutionSP>> r)
  // { return SLQueryResult(r.data->literal, r.data->clause, ResultSubstitutionSP((ResultSubstitution*)&*r.unif.unwrapOrElse([](){return RobSubstitutionSP();}))); }


  Stack<SubstitutionTree> _trees;
};

};

#endif /* __LiteralSubstitutionTree__ */
