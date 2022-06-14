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
 * @file TypeSubstitutionTree.hpp
 * Defines class TypeSubstitutionTree.
 */


#ifndef __TypeSubstitutionTree__
#define __TypeSubstitutionTree__


#include "Kernel/Renaming.hpp"
#include "Lib/SkipList.hpp"
#include "Lib/BiMap.hpp"

#include "Index.hpp"
#include "TermIndexingStructure.hpp"
#include "SubstitutionTree.hpp"

namespace Indexing {

template<class LeafData_>
class TypeSubstitutionTree
: public TermIndexingStructure<LeafData_>, Indexing::SubstitutionTree<LeafData_>
{
  using LeafData = LeafData_;
  using SubstitutionTree        = Indexing::SubstitutionTree<LeafData>;
  using TermIndexingStructure   = Indexing::TermIndexingStructure<LeafData>;
  using TermQueryResultIterator = VirtualIterator<TermQueryResult<LeafData>>;
  using QueryResult                 = typename SubstitutionTree::QueryResult;
  using BindingMap                  = typename SubstitutionTree::BindingMap;
  using Node                        = typename SubstitutionTree::Node;
  using FastInstancesIterator       = typename SubstitutionTree::FastInstancesIterator;
  using FastGeneralizationsIterator = typename SubstitutionTree::FastGeneralizationsIterator;
  using UnificationsIterator        = typename SubstitutionTree::UnificationsIterator;
  using LDIterator                  = typename SubstitutionTree::LDIterator;
  using LDComparator                = typename SubstitutionTree::LDComparator;
  using Leaf                        = typename SubstitutionTree::Leaf;
  using LeafIterator                = typename SubstitutionTree::LeafIterator;
public:
  CLASS_NAME(TypeSubstitutionTree);
  USE_ALLOCATOR(TypeSubstitutionTree);

  TypeSubstitutionTree();

  void insert(LeafData ld) final override { handleTerm(std::move(ld), true); }
  void remove(LeafData ld) final override { handleTerm(std::move(ld), false); }
  void handleTerm(LeafData ld, bool insert);


  // TermQueryResultIterator getUnifications(TermList sort, bool retrieveSubstitutions) final override;
  TermQueryResultIterator getUnifications(TermList sort, bool retrieveSubstitutions) final override { NOT_IMPLEMENTED; }

  TermQueryResultIterator getUnifications(TermList sort, TermList trm, 
    bool retrieveSubstitutions);

#if VDEBUG
  virtual void markTagged() final override { SubstitutionTree::markTagged();}
#endif
  
private:
  using TermIndexingStructure::insert; // state explicitly that "insert(TermList sort, LeafData ld);" is not meant to be an overload of any of the parent's inserts

  struct TermQueryResultFn;

  template<class Iterator>
  TermQueryResultIterator getResultIterator(Term* term,
	  bool retrieveSubstitutions);

  struct LDToTermQueryResultFn;
  struct LDToTermQueryResultWithSubstFn;
  struct LeafToLDIteratorFn;
  struct UnifyingContext;
  struct VarUnifFn;
  struct ToTypeSubFn;

  template<class LDIt>
  TermQueryResultIterator ldIteratorToTQRIterator(LDIt ldIt,
	  TermList queryTerm, bool retrieveSubstitutions);

  TermQueryResultIterator getAllUnifyingIterator(TermList trm,
	  bool retrieveSubstitution);

  inline
  unsigned getRootNodeIndex(Term* t)
  {
    return t->functor();
  }

  void normalize(Renaming& normalizer, DefaultLeafData& ld)
  { normalizer.normalizeVariables(ld.term); }

  template<class LD>
  void normalize(Renaming& normalizer, LD& ld)
  { }


  typedef SkipList<LeafData,LDComparator> LDSkipList;
  LDSkipList _vars;
};

};

#include "Indexing/TypeSubstitutionTree.cpp"

#endif /* __TypeSubstitutionTree__ */
