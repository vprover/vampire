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
#include "Lib/PairUtils.hpp"

#include "Index.hpp"
#include "TermIndexingStructure.hpp"
#include "TypeSubstitutionTree.hpp"
#include "SubstitutionTree.hpp"

namespace Indexing {

/*
 * Note that unlike LiteralSubstitutionTree, TermSubstitutionTree does
 * not (yet) carry out sort checking when attempting to find unifiers, generalisations
 * or instances. In particular, if the query or result is a variable, it is the callers'
 * responsibility to ensure that the sorts are unifiable/matchable
 */

template<class LeafData_ = DefaultTermLeafData>
class TermSubstitutionTree
: public TermIndexingStructure<LeafData_>, Indexing::SubstitutionTree<LeafData_>
{
  using SubstitutionTree        = Indexing::SubstitutionTree<LeafData_>;
  using TermIndexingStructure   = Indexing::TermIndexingStructure<LeafData_>;
  using TypeSubstitutionTree    = Indexing::TypeSubstitutionTree<LeafData_>;
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

  TermSubstitutionTree(MismatchHandler* hndlr = 0);

  void insert(LeafData d) final override { handleTerm(d, /* insert */ true); }
  // TODO use (LeafData const& d) here
  void remove(LeafData d) final override { handleTerm(d, /* insert */ false); }

  bool generalizationExists(TermList t) final override;


  TermQueryResultIterator getUnifications(TermList t,
	  bool retrieveSubstitutions) final override;

  TermQueryResultIterator getUnificationsUsingSorts(TermList t, TermList sort,
    bool retrieveSubstitutions) final override;

  TermQueryResultIterator getGeneralizations(TermList t,
	  bool retrieveSubstitutions) final override;

  TermQueryResultIterator getInstances(TermList t,
	  bool retrieveSubstitutions) final override;

private:

  void handleTerm(LeafData, bool insert);
  void handleTerm(TermList t, Literal* lit, Clause* cls, bool insert);
  bool constraintTermHandled(TermList t, LeafData ld, bool insert);

  struct TermQueryResultFn;

  template<class Iterator>
  TermQueryResultIterator getResultIterator(Term* term,
	  bool retrieveSubstitutions);

  struct LDToTermQueryResultFn;
  struct LDToTermQueryResultWithSubstFn;
  struct LeafToLDIteratorFn;
  struct UnifyingContext;

  template<class LDIt>
  TermQueryResultIterator ldIteratorToTQRIterator(LDIt ldIt,
	  TermList queryTerm, bool retrieveSubstitutions);

  TermQueryResultIterator getAllUnifyingIterator(TermList trm,
	  bool retrieveSubstitutions);

  inline
  unsigned getRootNodeIndex(Term* t)
  {
    return t->functor();
  }

  virtual std::ostream& output(std::ostream& out) const final override;

  typedef SkipList<LeafData,typename SubstitutionTree::LDComparator> LDSkipList;
  LDSkipList _vars;

  /* 
   * Used to store terms that could be part of constraints
   * For example $sum(X, Y) will be stored in _constraintTerms
   */
  TypeSubstitutionTree* _constraintTerms;
  MismatchHandler* _handler;
};

} // namespace Indexing

#include "Indexing/TermSubstitutionTree.cpp"

#endif /* __TermSubstitutionTree__ */
