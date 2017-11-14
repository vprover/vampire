
/*
 * File LiteralSubstitutionTree.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file LiteralSubstitutionTree.hpp
 * Defines class LiteralSubstitutionTree.
 */


#ifndef __LiteralSubstitutionTree__
#define __LiteralSubstitutionTree__

#include "LiteralIndexingStructure.hpp"
#include "SubstitutionTree.hpp"

namespace Indexing {

class LiteralSubstitutionTree
: public LiteralIndexingStructure, SubstitutionTree
{
public:
  CLASS_NAME(LiteralSubstitutionTree);
  USE_ALLOCATOR(LiteralSubstitutionTree);

  LiteralSubstitutionTree(bool useC=false);

  void insert(Literal* lit, Clause* cls);
  void remove(Literal* lit, Clause* cls);
  void handleLiteral(Literal* lit, Clause* cls, bool insert);

  SLQueryResultIterator getAll();

  SLQueryResultIterator getUnifications(Literal* lit,
	  bool complementary, bool retrieveSubstitutions);

  SLQueryResultIterator getUnificationsWithConstraints(Literal* lit,
          bool complementary, bool retrieveSubstitutions);

  SLQueryResultIterator getGeneralizations(Literal* lit,
	  bool complementary, bool retrieveSubstitutions);

  SLQueryResultIterator getInstances(Literal* lit,
	  bool complementary, bool retrieveSubstitutions);

  SLQueryResultIterator getVariants(Literal* lit,
	  bool complementary, bool retrieveSubstitutions);

#if VDEBUG
  virtual void markTagged(){ SubstitutionTree::markTagged();}
  vstring toString() {return SubstitutionTree::toString();}
#endif

private:
  struct SLQueryResultFunctor;
  struct LDToSLQueryResultFn;
  struct LDToSLQueryResultWithSubstFn;
  struct UnifyingContext;
  struct PropositionalLDToSLQueryResultWithSubstFn;
  struct LeafToLDIteratorFn;

  struct EqualitySortFilter;

  template<class Iterator>
  SLQueryResultIterator getResultIterator(Literal* lit,
	  bool complementary, bool retrieveSubstitutions, bool useConstraints);

  unsigned getRootNodeIndex(Literal* t, bool complementary=false);
};

};

#endif /* __LiteralSubstitutionTree__ */
