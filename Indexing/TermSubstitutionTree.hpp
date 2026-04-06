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
#include "Kernel/UnificationWithAbstraction.hpp"
#include "Kernel/TypedTermList.hpp"

#include "Index.hpp"
#include "TermIndexingStructure.hpp"
#include "SubstitutionTree.hpp"

namespace Indexing {

/*
 * As of 22/03/2023 TermSubstitutionTrees carry our type checking.
 * Thus, there is no need to check whether the type of returned terms match those of the query
 * as this is now done within the tree.
 */


/** A wrapper class around SubstitutionTree that makes it usable  as a TermIndexingStructure */
template<class LeafData_>
class TermSubstitutionTree
: public TermIndexingStructure<LeafData_>
{
  using SubstitutionTree            = Indexing::SubstitutionTree<LeafData_>;
  using TermIndexingStructure       = Indexing::TermIndexingStructure<LeafData_>;
  using BindingMap                  = typename SubstitutionTree::BindingMap;
  using Node                        = typename SubstitutionTree::Node;
  using FastInstancesIterator       = typename SubstitutionTree::FastInstancesIterator;
  using FastGeneralizationsIterator = typename SubstitutionTree::FastGeneralizationsIterator;
  using LDIterator                  = typename SubstitutionTree::LDIterator;
  using Leaf                        = typename SubstitutionTree::Leaf;
  using LeafIterator                = typename SubstitutionTree::LeafIterator;

  Indexing::SubstitutionTree<LeafData_> _inner;
public:
  using LeafData = LeafData_;
  
  TermSubstitutionTree()
    : _inner()
    { }

  void handle(LeafData d, bool insert) final
  { _inner.handle(std::move(d), insert); }

private:

  template<class Iterator, class... Args>
  auto getResultIterator(TypedTermList query, bool retrieveSubstitutions, Args... args)
  { return iterTraits(_inner.template iterator<Iterator>(query, retrieveSubstitutions, /* reversed */  false, std::move(args)...))
      ; }

  bool generalizationExists(TermList t) override
  { return t.isVar() ? false : _inner.generalizationExists(TypedTermList(t.term())); }

  void output(std::ostream& out) const final { out << *this; }

  friend std::ostream& operator<<(std::ostream& out, TermSubstitutionTree<LeafData_> const& self)
  { return out << self._inner; }
  friend std::ostream& operator<<(std::ostream& out, Output::Multiline<TermSubstitutionTree<LeafData_>> const& self)
  { return out << Output::multiline(self.self._inner, self.indent); }

public:
  VirtualIterator<Indexing::QueryRes<ResultSubstitutionSP, LeafData_>> getInstances(TypedTermList t, bool retrieveSubstitutions) final
  { return pvi(getResultIterator<FastInstancesIterator>(t, retrieveSubstitutions)); }

  VirtualIterator<QueryRes<ResultSubstitutionSP, LeafData>> getGeneralizations(TypedTermList t, bool retrieveSubstitutions) final
  { return pvi(getResultIterator<FastGeneralizationsIterator>(t, retrieveSubstitutions)); }


  VirtualIterator<QueryRes<AbstractingUnifier*, LeafData>> getUwa(TypedTermList t, Options::UnificationWithAbstraction uwa, bool fixedPointIteration) final
  { return pvi(getResultIterator<typename SubstitutionTree::template Iterator<RetrievalAlgorithms::UnificationWithAbstraction<AbstractingUnifier, RetrievalAlgorithms::DefaultVarBanks>>>(t, /* retrieveSubstitutions */ true, AbstractingUnifier::empty(AbstractionOracle(uwa)), AbstractionOracle(uwa), fixedPointIteration)); }

  template<class VarBanks>
  VirtualIterator<QueryRes<AbstractingUnifier*, LeafData>> getUwa(AbstractingUnifier* state, TypedTermList t, Options::UnificationWithAbstraction uwa, bool fixedPointIteration)
  { return pvi(getResultIterator<typename SubstitutionTree::template Iterator<RetrievalAlgorithms::UnificationWithAbstraction<AbstractingUnifier*, VarBanks>>>(t, /* retrieveSubstitutions */ true, state, AbstractionOracle(uwa), fixedPointIteration)); }

  VirtualIterator<QueryRes<ResultSubstitutionSP, LeafData>> getUnifications(TypedTermList t, bool retrieveSubstitutions) override
  { return pvi(getResultIterator<typename SubstitutionTree::template Iterator<RetrievalAlgorithms::RobUnification<RetrievalAlgorithms::DefaultVarBanks>>>(t, retrieveSubstitutions)); }
};

} // namespace Indexing

#endif /* __TermSubstitutionTree__ */
