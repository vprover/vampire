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
  template<class UnificationAlgorithm>
  using UnificationsIterator        = typename SubstitutionTree::template UnificationsIterator<UnificationAlgorithm>;
  using LDIterator                  = typename SubstitutionTree::LDIterator;
  using Leaf                        = typename SubstitutionTree::Leaf;
  using LeafIterator                = typename SubstitutionTree::LeafIterator;


public:
  CLASS_NAME(LiteralSubstitutionTree);
  USE_ALLOCATOR(LiteralSubstitutionTree);

  LiteralSubstitutionTree()
    : _trees(env.signature->predicates() * 2)
    { }

  void handle(LeafData ld, bool insert) final override
  { getTree(ld.key(), /* complementary */ false).handle(std::move(ld), insert); }

  void output(std::ostream& out, bool enableMultiline, unsigned indent) final override 
  { enableMultiline ? out << multiline(*this, indent) : out << *this; }

  VirtualIterator<LeafData> getAll() final override
  {
    CALL("LiteralSubstitutionTree::getAll");

    return pvi(
          iterTraits(getRangeIterator((unsigned long)0, _trees.size()))
           .flatMap([this](auto i) { return LeafIterator(&_trees[i]); })
           .flatMap([](Leaf* l) { return l->allChildren(); })
           // TODO get rid of copying data here
           .map([](LeafData const* ld) { return *ld; })
        );
  }

  VirtualIterator<QueryRes<ResultSubstitutionSP, LeafData_>> getUnifications(Literal* lit, bool complementary, bool retrieveSubstitutions) final override
  { return getResultIterator<UnificationsIterator<UnificationAlgorithms::RobUnification>>(lit, complementary, retrieveSubstitutions); }


  VirtualIterator<QueryRes<ResultSubstitutionSP, LeafData>> getGeneralizations(Literal* lit, bool complementary, bool retrieveSubstitutions) final override
  { return getResultIterator<FastGeneralizationsIterator>(lit, complementary, retrieveSubstitutions); }

  VirtualIterator<QueryRes<ResultSubstitutionSP, LeafData>> getInstances(Literal* lit, bool complementary, bool retrieveSubstitutions) final override
  { return getResultIterator<FastInstancesIterator>(lit, complementary, retrieveSubstitutions); }

  VirtualIterator<QueryRes<ResultSubstitutionSP, LeafData>> getVariants(Literal* query, bool complementary, bool retrieveSubstitutions) final override
  {
    return pvi(iterTraits(getTree(query, complementary).getVariants(query, retrieveSubstitutions))
          .map([](auto qr) { return queryRes(std::move(qr.unif), qr.data); }));
  }


private:
  static unsigned idxToFunctor(unsigned idx) { return idx / 2; }
  static bool idxIsNegative(unsigned idx) { return idx % 2; }
  static unsigned toIdx(unsigned f, bool isNegative) { return f * 2 + isNegative; }


  template<class Algo>
  using UwaIter = typename Indexing::SubstitutionTree<LeafData_>::template UnificationsIterator<Algo>;

  auto nopostproUwa(Literal* lit, bool complementary, Options::UnificationWithAbstraction uwa)
  { return getResultIterator<UwaIter<UnificationAlgorithms::UnificationWithAbstraction>>(lit, complementary, /* retrieveSubstitutions */ true, MismatchHandler(uwa)); }

  auto postproUwa(Literal* lit, bool complementary, Options::UnificationWithAbstraction uwa)
  { return pvi(iterTraits(getResultIterator<UwaIter<UnificationAlgorithms::UnificationWithAbstractionWithPostprocessing>>(lit, complementary, /* retrieveSubstitutions */ true, MismatchHandler(uwa)))
    .filterMap([](auto r)
        { return r.unifier.fixedPointIteration().map([&](AbstractingUnifier* unif) { return queryRes(unif, r.data); }); })); }


public:

  VirtualIterator<QueryRes<AbstractingUnifier*, LeafData>> getUwa(Literal* lit, bool complementary, Options::UnificationWithAbstraction uwa, bool fixedPointIteration) final override
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
  friend std::ostream& operator<<(std::ostream& out, OutputMultiline<LiteralSubstitutionTree<LeafData_>> const& self)
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
    auto pos = lit->functor() * 2;
    auto neg = pos + 1;
    auto idx = complementary ? (lit->isPositive() ? neg : pos)
                             : (lit->isPositive() ? pos : neg);
    while (idx >= _trees.size()) {
      auto p = _trees.size() / 2;
      auto arity = env.signature->isEqualityPredicate(p) ? 3 // equality is special case because it has an implicit type argument not present in the signature
                                                         : env.signature->getPredicate(p)->arity();
      _trees.push(SubstitutionTree(arity));
    }
    return _trees[idx];
  }


  template<class Iterator, class... Args>
  auto getResultIterator(Literal* lit, bool complementary, bool retrieveSubstitutions, Args... args)
  {
    CALL("LiteralSubstitutionTree::getResultIterator");

    auto iter = [=](bool reversed) 
      { return iterTraits(getTree(lit, complementary).template iterator<Iterator>(lit, retrieveSubstitutions, reversed, args...)) ; };

    auto filterResults = [=](auto it) { 
      return pvi(
          std::move(it)
          .map([](auto r) { return queryRes(std::move(r.unif), r.data); })
          ); 
    };
    return !lit->commutative() 
      ?  filterResults(iter( /* reversed */ false))
      :  filterResults(concatIters(
          iter( /* reversed */ false),
          iter( /* reversed */ true)
        ));
  }

  Stack<SubstitutionTree> _trees;
};

};

#endif /* __LiteralSubstitutionTree__ */
