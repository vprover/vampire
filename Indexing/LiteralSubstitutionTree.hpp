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
#include "Kernel/UnificationWithAbstraction.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/VirtualIterator.hpp"
#include "LiteralIndexingStructure.hpp"
#include "SubstitutionTree.hpp"
#include "Kernel/Signature.hpp"

namespace Indexing {

/** A wrapper class around SubstitutionTree that makes it usable  as a LiteralIndexingStructure */
template<class LeafData_>
class LiteralSubstitutionTree
: public LiteralIndexingStructure<LeafData_>
{
  using SubstitutionTree = Indexing::SubstitutionTree<LeafData_>;
  using LeafData         = LeafData_;
  using BindingMap                  = typename SubstitutionTree::BindingMap;
  using Node                        = typename SubstitutionTree::Node;
  using FastInstancesIterator       = typename SubstitutionTree::FastInstancesIterator;
  using FastGeneralizationsIterator = typename SubstitutionTree::FastGeneralizationsIterator;
  using LDIterator                  = typename SubstitutionTree::LDIterator;
  using Leaf                        = typename SubstitutionTree::Leaf;
  using LeafIterator                = typename SubstitutionTree::LeafIterator;

public:
  LiteralSubstitutionTree()
    : _trees(Lib::env.signature->predicates() * 2)
    { }

  void handle(LeafData ld, bool insert) final override
  { getTree(ld.key(), /* complementary */ false).handle(std::move(ld), insert); }

  Lib::VirtualIterator<LeafData> getAll() final override
  {
    return pvi(
          iterTraits(getRangeIterator((unsigned long)0, _trees.size()))
           .flatMap([this](auto i) { return LeafIterator(_trees[i].get()); })
           .flatMap([](Leaf* l) { return l->allChildren(); })
           // TODO get rid of copying data here
           .map([](LeafData const* ld) { return *ld; })
        );
  }

  Lib::VirtualIterator<QueryRes<ResultSubstitutionSP, LeafData_>> getUnifications(Literal* lit, bool complementary, bool retrieveSubstitutions) final override
  { return pvi(getResultIterator<typename SubstitutionTree::template Iterator<RetrievalAlgorithms::RobUnification>>(lit, complementary, retrieveSubstitutions)); }

  Lib::VirtualIterator<QueryRes<ResultSubstitutionSP, LeafData>> getGeneralizations(Literal* lit, bool complementary, bool retrieveSubstitutions) final override
  { return pvi(getResultIterator<FastGeneralizationsIterator>(lit, complementary, retrieveSubstitutions)); }

  Lib::VirtualIterator<QueryRes<ResultSubstitutionSP, LeafData>> getInstances(Literal* lit, bool complementary, bool retrieveSubstitutions) final override
  { return pvi(getResultIterator<FastInstancesIterator>(lit, complementary, retrieveSubstitutions)); }

  Lib::VirtualIterator<QueryRes<ResultSubstitutionSP, LeafData>> getVariants(Literal* query, bool complementary, bool retrieveSubstitutions) final override
  {
    return pvi(iterTraits(getTree(query, complementary).getVariants(query, retrieveSubstitutions)));
  }

private:
  /** encodes functor and polarity into one number, so it can be used as an index in the array _trees
   * The inverse functions to this are `idxIsNegative` and `idxToFunctor` */
  static unsigned toIdx(unsigned f, bool isNegative) { return f * 2 + isNegative; }
  /** `toIdx` encodes functor and polarity into one number, so it can be used as an index in the array _trees
   * The inverse functions to this are `idxIsNegative` and `idxToFunctor` */
  static unsigned idxToFunctor(unsigned idx) { return idx / 2; }
  /** `toIdx` encodes functor and polarity into one number, so it can be used as an index in the array _trees
   * The inverse functions to this are `idxIsNegative` and `idxToFunctor` */
  static bool idxIsNegative(unsigned idx) { return idx % 2; }

  template<class Iterator, class... Args>
  auto getResultIterator(Literal* lit, bool complementary, bool retrieveSubstitutions, Args... args)
  {
    auto tree = &getTree(lit, complementary);

    auto iter = [tree, lit, retrieveSubstitutions, &args...](bool reversed) 
      { return tree->template iterator<Iterator>(lit, retrieveSubstitutions, reversed, args...); };

    return ifElseIter(
        tree->isEmpty(), [&]() { return Lib::VirtualIterator<ELEMENT_TYPE(Iterator)>::getEmpty(); }, 
                         [&]() { return ifElseIter(!lit->commutative(), 
                                 [&]() { return iter(/* reverse */ false); },
                                 [&]() { return concatIters(iter(/* reverse */ false), iter(/* reverse */ true)); }); }
        );
    // if (tree.isEmpty()) {
    //
    // }

    // return ifElseIter(
    //     !lit->commutative(),
    //     [&]() { return iter( /* reversed */ false); },
    //     [&]() { return concatIters(
    //                 iter( /* reversed */ false),
    //                 iter( /* reversed */ true)
    //                 ); }
    //     );
  }

public:

  Lib::VirtualIterator<QueryRes<AbstractingUnifier*, LeafData>> getUwa(Literal* lit, bool complementary, Options::UnificationWithAbstraction uwa, bool fixedPointIteration) final override
  { return pvi(getResultIterator<typename SubstitutionTree::template Iterator<RetrievalAlgorithms::UnificationWithAbstraction>>(lit, complementary, /* retrieveSubstitutions */ true, AbstractionOracle(uwa), fixedPointIteration)); }

  friend std::ostream& operator<<(std::ostream& out, LiteralSubstitutionTree const& self)
  { 
    int i = 0;
    out << "{ ";
    for (auto& t : self._trees) {
      if (!t->isEmpty()) {
        auto f = Lib::env.signature->getPredicate(idxToFunctor(i));
        if (idxIsNegative(i)) out << "~";
        out << *f << "(" << *t << "), "; 
      }
      i++;
    }
    return out << "} ";
  }
  friend std::ostream& operator<<(std::ostream& out, OutputMultiline<LiteralSubstitutionTree> const& self)
  { 
    int i = 0;
    out << "{ " << std::endl;
    for (auto& t : self.self._trees) {
      if (!t->isEmpty()) {
        auto f = Lib::env.signature->getPredicate(idxToFunctor(i));
        OutputMultiline<LiteralSubstitutionTree>::outputIndent(out, self.indent);
        out << (idxIsNegative(i) ? "~" : " ") << *f << "(" << multiline(*t, self.indent + 1) << ")" << std::endl; 
      }
      i++;
    }
    return out << "} ";
  }

  virtual void output(std::ostream& out, Lib::Option<unsigned> multilineIndent) const override {
    if (multilineIndent) {
      out << multiline(*this, *multilineIndent);
    } else {
      out << *this;
    }
  }


private:
  SubstitutionTree& getTree(Literal* lit, bool complementary)
  {
    auto findNegative = complementary ? lit->isPositive() : lit->isNegative();
    auto idx = toIdx(lit->functor(), findNegative);
    while (idx >= _trees.size()) {
      _trees.push(std::make_unique<SubstitutionTree>());
    }
    return *_trees[idx];
  }

  Lib::Stack<std::unique_ptr<SubstitutionTree>> _trees;
};

};

#endif /* __LiteralSubstitutionTree__ */
