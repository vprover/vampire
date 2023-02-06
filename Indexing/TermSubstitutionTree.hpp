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


#include "Kernel/Renaming.hpp"
#include "Lib/SkipList.hpp"
#include "Lib/BiMap.hpp"

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
  using SubstitutionTree        = Indexing::SubstitutionTree<LeafData_>;
  using TermIndexingStructure   = Indexing::TermIndexingStructure<LeafData_>;
  using TermQueryResultIterator = VirtualIterator<TermQueryResult<LeafData_>>;
  using BindingMap                  = typename SubstitutionTree::BindingMap;
  using Node                        = typename SubstitutionTree::Node;
  using FastInstancesIterator       = typename SubstitutionTree::FastInstancesIterator;
  using FastGeneralizationsIterator = typename SubstitutionTree::FastGeneralizationsIterator;
  using UnificationsIterator        = typename SubstitutionTree::UnificationsIterator;
  using QueryResult                 = typename SubstitutionTree::QueryResult;
  using LDIterator                  = typename SubstitutionTree::LDIterator;
  using Leaf                        = typename SubstitutionTree::Leaf;
  using LeafIterator                = typename SubstitutionTree::LeafIterator;
public:
  using LeafData = LeafData_;
  CLASS_NAME(TermSubstitutionTree);
  USE_ALLOCATOR(TermSubstitutionTree);
  
  TermSubstitutionTree(bool useC=false, bool replaceFunctionalSubterms = false)
    : _inner(useC, replaceFunctionalSubterms, /* reservedSpecialVars */ 2 /* S0 -> term, S1 -> sort */ )
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
      .map([](QueryResult qr) { return TermQueryResult<LeafData>(*qr.data, qr.subst, qr.constr); }) ; 
  }

  friend std::ostream& operator<<(std::ostream& out, TermSubstitutionTree const& self)
  { return out << (SubstitutionTree const&) self; }
  friend std::ostream& operator<<(std::ostream& out, OutputMultiline<TermSubstitutionTree> const& self)
  { return out << multiline((SubstitutionTree const&) self.self); }
public:
  TermQueryResultIterator getInstances(TermList t, bool retrieveSubstitutions) final override
  { return pvi(getResultIterator<FastInstancesIterator>(t, retrieveSubstitutions, /* constraints */ false)); }

  TermQueryResultIterator getGeneralizations(TermList t, bool retrieveSubstitutions) final override
  { return pvi(getResultIterator<FastGeneralizationsIterator>(t, retrieveSubstitutions, /* constraints */ false)); }

  TermQueryResultIterator getUnifications(TermList t, bool retrieveSubstitutions, bool withConstraints) final override
  { return pvi(getResultIterator<UnificationsIterator>(t, retrieveSubstitutions, withConstraints)); }

  TermQueryResultIterator getUnificationsUsingSorts(TypedTermList tt, bool retrieveSubstitutions, bool withConstr) final override
  { return pvi(getResultIterator<UnificationsIterator>(tt, retrieveSubstitutions, withConstr)); }

  Indexing::SubstitutionTree<LeafData_> _inner;
};

} // namespace Indexing

#endif /* __TermSubstitutionTree__ */
