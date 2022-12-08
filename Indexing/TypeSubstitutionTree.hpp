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
: SubstitutionTree
{
public:
  CLASS_NAME(TypeSubstitutionTree);
  USE_ALLOCATOR(TypeSubstitutionTree);

  TypeSubstitutionTree();

  void handleTerm(TermList t, LeafData ld, bool insert);
  TermQueryResultIterator getUnifications(TermList sort, TermList trm, bool retrieveSubstitutions);

#if VDEBUG
  virtual void markTagged() override { SubstitutionTree::markTagged();}
#endif
  friend std::ostream& operator<<(std::ostream& out, TypeSubstitutionTree const& self)
  { return out << "TypeSubstitutionTree(" << (SubstitutionTree const&) self << ")"; }
  
private:

  struct ToTypeSubFn;

};

};

#endif /* __TypeSubstitutionTree__ */
