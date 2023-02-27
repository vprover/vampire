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
#include "Kernel/MismatchHandler.hpp"
#include "Kernel/Renaming.hpp"
#include "Kernel/TypedTermList.hpp"
#include "Lib/SkipList.hpp"
#include "Lib/PairUtils.hpp"

#include "Index.hpp"
#include "TermIndexingStructure.hpp"
#include "SubstitutionTree.hpp"

namespace Indexing {

/*
 * Note that unlike LiteralSubstitutionTree, TermSubstitutionTree does
 * not (yet) carry out sort checking when attempting to find unifiers, generalisations
 * or instances. In particular, if the query or result is a variable, it is the callers'
 * responsibility to ensure that the sorts are unifiable/matchable
 * (edit: if the caller inserts a TypedTermList instead of a TermList, this will be handled automatically.)
 */


/** A wrapper class around SubstitutionTree that makes it usable  as a TermIndexingStructure */
template<class LeafData_ = DefaultTermLeafData>
class TermSubstitutionTree
: public TermIndexingStructure<LeafData_>
{
  using SubstitutionTree            = Indexing::SubstitutionTree<LeafData_>;
  using TermIndexingStructure       = Indexing::TermIndexingStructure<LeafData_>;
  using BindingMap                  = typename SubstitutionTree::BindingMap;
  using Node                        = typename SubstitutionTree::Node;
  using FastInstancesIterator       = typename SubstitutionTree::FastInstancesIterator;
  using FastGeneralizationsIterator = typename SubstitutionTree::FastGeneralizationsIterator;
  template<class Algo>
  using UnificationsIterator        = typename SubstitutionTree::template UnificationsIterator<Algo>;
  using LDIterator                  = typename SubstitutionTree::LDIterator;
  using Leaf                        = typename SubstitutionTree::Leaf;
  using LeafIterator                = typename SubstitutionTree::LeafIterator;

  Indexing::SubstitutionTree<LeafData_> _inner;
public:
  using LeafData = LeafData_;
  CLASS_NAME(TermSubstitutionTree);
  USE_ALLOCATOR(TermSubstitutionTree);
  
  TermSubstitutionTree()
    : _inner(/* reservedSpecialVars */ 2 /* S0 -> term, S1 -> sort */ )
    { }

  void handle(LeafData d, bool insert) final override
  { _inner.handle(std::move(d), insert); }

  bool generalizationExists(TermList t) final override
  { return t.isVar() ? false : _inner.generalizationExists(t); }

private:

  template<class Iterator, class TypedOrUntypedTermList> 
  auto getResultIterator(TypedOrUntypedTermList query, bool retrieveSubstitutions, bool withConstraints)
  { 
    return iterTraits(_inner.template iterator<Iterator>(query, retrieveSubstitutions, withConstraints))
      .map([](auto qr) { return queryRes(std::move(qr.unifier), qr.data); }) ; 
  }

  virtual void output(std::ostream& out) const final override { out << *this; }


  template<class Iterator, class TypedOrUntypedTermList, class... Args>
  auto getResultIterator(TypedOrUntypedTermList query, bool retrieveSubstitutions, Args... args)
  { 
    return iterTraits(_inner.template iterator<Iterator>(query, retrieveSubstitutions, /* reversed */  false, std::move(args)...))
      .map([](auto qr) { return queryRes(std::move(qr.unif), qr.data); }) ; 
  }


  friend std::ostream& operator<<(std::ostream& out, TermSubstitutionTree<LeafData_> const& self)
  { return out << self._inner; }
  friend std::ostream& operator<<(std::ostream& out, OutputMultiline<TermSubstitutionTree<LeafData_>> const& self)
  { return out << multiline(self.self._inner, self.indent); }

  template<class Algo>
  using UwaIter = typename Indexing::SubstitutionTree<LeafData_>::template UnificationsIterator<Algo>;

  auto nopostproUwa(TypedTermList t, Options::UnificationWithAbstraction uwa)
  { return getResultIterator<UwaIter<UnificationAlgorithms::UnificationWithAbstraction>>(t, /* retrieveSubstitutions */ true, MismatchHandler(uwa)); }

  auto postproUwa(TypedTermList t, Options::UnificationWithAbstraction uwa)
  { return iterTraits(getResultIterator<UwaIter<UnificationAlgorithms::UnificationWithAbstractionWithPostprocessing>>(t, /* retrieveSubstitutions */ true, MismatchHandler(uwa)))
    .filterMap([](auto r)
        { return r.unifier.fixedPointIteration().map([&](AbstractingUnifier* unif) { return queryRes(unif, r.data); }); }); }

public:

  VirtualIterator<Indexing::QueryRes<ResultSubstitutionSP, LeafData_>> getInstances(TermList t, bool retrieveSubstitutions) final override
  { return pvi(getResultIterator<FastInstancesIterator>(t, retrieveSubstitutions)); }

  VirtualIterator<QueryRes<ResultSubstitutionSP, LeafData>> getGeneralizations(TermList t, bool retrieveSubstitutions) final override
  { return pvi(getResultIterator<FastGeneralizationsIterator>(t, retrieveSubstitutions)); }

  VirtualIterator<QueryRes<AbstractingUnifier*, LeafData>> getUwa(TypedTermList t, Options::UnificationWithAbstraction uwa, bool fixedPointIteration) final override
  { return fixedPointIteration ? pvi(  postproUwa(t, uwa))
                               : pvi(nopostproUwa(t, uwa)); }


  VirtualIterator<QueryRes<ResultSubstitutionSP, LeafData>> getUnifications(TermList t, bool retrieveSubstitutions) override
  { return pvi(getResultIterator<UnificationsIterator<UnificationAlgorithms::RobUnification>>(t, retrieveSubstitutions)); }

  VirtualIterator<QueryRes<ResultSubstitutionSP, LeafData>> getUnificationsUsingSorts(TypedTermList tt, bool retrieveSubstitutions) final override
  { return pvi(getResultIterator<UnificationsIterator<UnificationAlgorithms::RobUnification>>(tt, retrieveSubstitutions)); }

};

} // namespace Indexing

#endif /* __TermSubstitutionTree__ */
