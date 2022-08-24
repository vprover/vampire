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

// A substitution tree based indexing structure, that stores sorts in the tree
// and terms of the relevant sorts in the leaves.
// It is useful when we are interested in finding terms that can type unify, but 
// not necessarily term unify. For example it is used in unification with abstraction.


class TypeSubstitutionTree
: public TermIndexingStructure, SubstitutionTree
{
public:
  CLASS_NAME(TypeSubstitutionTree);
  USE_ALLOCATOR(TypeSubstitutionTree);

  TypeSubstitutionTree(MismatchHandler* hndlr = 0);

  void insert(TermList sort, LeafData ld);
  void remove(TermList sort, LeafData ld);
  void handleTerm(TermList t, LeafData ld, bool insert);
  void insert(TermList t, Literal* lit, Clause* cls){ NOT_IMPLEMENTED; }
  void remove(TermList t, Literal* lit, Clause* cls){ NOT_IMPLEMENTED; }


  TermQueryResultIterator getUnifications(TermList sort,
	  bool retrieveSubstitutions){ NOT_IMPLEMENTED; }

  // Returns all terms whose sort unifies with @param sort
  // @param trm is a term of sort sort. 
  // If @param trm is a variable, the resulting substitution is extending to be a term
  // substitution as well. Likewise if the result is a variable
  // If neither query nor result is a variable, attempt to create a
  // constraint between them
  TermQueryResultIterator getUnifications(TermList sort, TermList trm, 
    bool retrieveSubstitutions);

#if VDEBUG
  virtual void markTagged(){ SubstitutionTree::markTagged();}
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
  struct ToTermUnifier;
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

  MismatchHandler* _handler;
  typedef SkipList<LeafData,LDComparator> LDSkipList;
  LDSkipList _vars;
};

};

#endif /* __TypeSubstitutionTree__ */
