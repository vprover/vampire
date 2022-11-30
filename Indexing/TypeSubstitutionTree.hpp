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

class TypeSubstitutionTree
: public TermIndexingStructure, SubstitutionTree
{
public:
  CLASS_NAME(TypeSubstitutionTree);
  USE_ALLOCATOR(TypeSubstitutionTree);

  TypeSubstitutionTree();

  void insert(TermList sort, LeafData ld);
  void remove(TermList sort, LeafData ld);
  void handleTerm(TermList t, LeafData ld, bool insert);
  void insert(TermList t, Literal* lit, Clause* cls){ NOT_IMPLEMENTED; }
  void remove(TermList t, Literal* lit, Clause* cls){ NOT_IMPLEMENTED; }


  TermQueryResultIterator getUnifications(TermList sort, bool retrieveSubstitutions) override { NOT_IMPLEMENTED; }

  TermQueryResultIterator getUnifications(TermList sort, TermList trm, 
    bool retrieveSubstitutions);

#if VDEBUG
  virtual void markTagged(){ SubstitutionTree::markTagged();}
#endif
  
private:
  using TermIndexingStructure::insert; // state explicitly that "insert(TermList sort, LeafData ld);" is not meant to be an overload of any of the parent's inserts

  struct ToTypeSubFn;

};

};

#endif /* __TypeSubstitutionTree__ */
