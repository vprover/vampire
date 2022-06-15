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
  
  TermSubstitutionTree(bool useC=false, bool replaceFunctionalSubterms = false);

  void insert(LeafData d) final override { handleTerm(d, /* insert */ true); }
  void remove(LeafData d) final override { handleTerm(d, /* insert */ false); }

  bool generalizationExists(TermList t) final override;


  TermQueryResultIterator getUnifications(TermList t,
	  bool retrieveSubstitutions) final override;

  TermQueryResultIterator getUnificationsWithConstraints(TermList t,
    bool retrieveSubstitutions) final override;

  /*
   * A higher order concern (though it may be useful in other situations)
   */
  TermQueryResultIterator getUnificationsUsingSorts(TermList t, TermList sort,
    bool retrieveSubstitutions) final override;

  TermQueryResultIterator getGeneralizations(TermList t,
	  bool retrieveSubstitutions) final override;

  TermQueryResultIterator getInstances(TermList t,
	  bool retrieveSubstitutions) final override;

#if VDEBUG
  virtual void markTagged() final override { SubstitutionTree::markTagged();}
#endif

private:

  void handleTerm(LeafData, bool insert);

  struct TermQueryResultFn;

  template<class Iterator>
  TermQueryResultIterator getResultIterator(Term* term,
	  bool retrieveSubstitutions,bool withConstraints);

  struct LDToTermQueryResultFn;
  struct LDToTermQueryResultWithSubstFn;
  struct LeafToLDIteratorFn;
  struct UnifyingContext;

  template<class LDIt>
  TermQueryResultIterator ldIteratorToTQRIterator(LDIt ldIt,
	  TermList queryTerm, bool retrieveSubstitutions,
          bool withConstraints);

  TermQueryResultIterator getAllUnifyingIterator(TermList trm,
	  bool retrieveSubstitutions,bool withConstraints);

  inline
  unsigned getRootNodeIndex(Term* t)
  {
    return t->functor();
  }

  typedef SkipList<LeafData,typename SubstitutionTree::LDComparator> LDSkipList;
  LDSkipList _vars;

  //higher-order concerns
  bool _extByAbs;

  FuncSubtermMap _functionalSubtermMap;

  TypeSubstitutionTree* _funcSubtermsByType;

};

} // namespace Indexing

#include "Indexing/TermSubstitutionTree.cpp"

#endif /* __TermSubstitutionTree__ */
