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
 * @file TermSubstitutionTree.hpp
 * Defines class TermSubstitutionTree.
 */


#ifndef __TermSubstitutionTree__
#define __TermSubstitutionTree__


#include "Forwards.hpp"

#include "Lib/PairUtils.hpp"

#include "Kernel/HOL/Unifier.hpp"
#include "Kernel/UnificationWithAbstraction.hpp"
#include "Kernel/TypedTermList.hpp"

#include "Index.hpp"
#include "SubstitutionTree.hpp"

namespace Indexing {

/*
 * As of 22/03/2023 TermSubstitutionTrees carry our type checking.
 * Thus, there is no need to check whether the type of returned terms match those of the query
 * as this is now done within the tree.
 */


/** A wrapper class around SubstitutionTree that makes it usable for indexing terms. */
template<class LeafData_>
class TermSubstitutionTree
{
  using SubstitutionTree            = Indexing::SubstitutionTree<LeafData_>;
  using BindingMap                  = typename SubstitutionTree::BindingMap;
  using Node                        = typename SubstitutionTree::Node;
  using FastInstancesIterator       = typename SubstitutionTree::FastInstancesIterator;
  using LDIterator                  = typename SubstitutionTree::LDIterator;
  using Leaf                        = typename SubstitutionTree::Leaf;
  using LeafIterator                = typename SubstitutionTree::LeafIterator;

  Indexing::SubstitutionTree<LeafData_> _inner;
public:
  using LeafData = LeafData_;
  
  TermSubstitutionTree()
    : _inner()
    { }

  void handle(LeafData d, bool insert)
  { _inner.handle(std::move(d), insert); }

  void insert(LeafData data) { handle(std::move(data), /* insert */ true ); }
  void remove(LeafData data) { handle(std::move(data), /* insert */ false); }

private:

  template<class Iterator, class... Args>
  auto getResultIterator(TypedTermList query, bool retrieveSubstitutions, Args... args)
  { return iterTraits(_inner.template iterator<Iterator>(query, retrieveSubstitutions, /* reversed */  false, std::move(args)...))
      ; }

  friend std::ostream& operator<<(std::ostream& out, TermSubstitutionTree<LeafData_> const& self)
  { return out << self._inner; }
  friend std::ostream& operator<<(std::ostream& out, Output::Multiline<TermSubstitutionTree<LeafData_>> const& self)
  { return out << Output::multiline(self.self._inner, self.indent); }

public:
  auto getInstances(TypedTermList t, bool retrieveSubstitutions)
  { return pvi(getResultIterator<FastInstancesIterator>(t, retrieveSubstitutions)); }

  auto getUwa(TypedTermList t, Options::UnificationWithAbstraction uwa, bool fixedPointIteration, bool funcExt)
  {
    AbstractionOracle oracle(uwa, funcExt);
    return pvi(getResultIterator<typename SubstitutionTree::template Iterator<RetrievalAlgorithms::UnificationWithAbstraction<AbstractingUnifier, RetrievalAlgorithms::DefaultVarBanks>>>(t, /* retrieveSubstitutions */ true, AbstractingUnifier::empty(oracle), oracle, fixedPointIteration));
  }

  // This should be used on HOL problems as it has potential overhead, but it does not necessarily
  // perform HO-unification, so the `uwa` argument is still meaningful.
  // TODO(HOL): the difference between getUwa and getUwaHOL is somewhat opaque at the moment, iron this out and make the overhead small when using `uwa!=hol`.
  auto getUwaHOL(TypedTermList t, Options::UnificationWithAbstraction uwa, bool fixedPointIteration, unsigned hoUnifDepth, bool funcExt)
  {
    return pvi(iterTraits(getUwa(t, uwa, fixedPointIteration, funcExt))
      .flatMap([hoUnifDepth,funcExt](QueryRes<AbstractingUnifier*, LeafData> qr) { return pvi(pushPairIntoRightIterator(qr, vi(new HOL::AbstractingWrapper(qr.unifier, hoUnifDepth, funcExt)))); })
      .map([](auto arg) { return queryRes(arg.second, arg.first.data); }));
  }

  template<class VarBanks>
  auto getUwa(AbstractingUnifier* state, TypedTermList t, Options::UnificationWithAbstraction uwa, bool fixedPointIteration)
  { return pvi(getResultIterator<typename SubstitutionTree::template Iterator<RetrievalAlgorithms::UnificationWithAbstraction<AbstractingUnifier*, VarBanks>>>(t, /* retrieveSubstitutions */ true, state, AbstractionOracle(uwa), fixedPointIteration)); }

  auto getUnifications(TypedTermList t, bool retrieveSubstitutions)
  { return pvi(getResultIterator<typename SubstitutionTree::template Iterator<RetrievalAlgorithms::RobUnification<RetrievalAlgorithms::DefaultVarBanks>>>(t, retrieveSubstitutions)); }
};

} // namespace Indexing

#endif /* __TermSubstitutionTree__ */
