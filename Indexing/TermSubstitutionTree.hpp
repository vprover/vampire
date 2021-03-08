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
#include "SubstitutionTree.hpp"

namespace Indexing {

class TermSubstitutionTree
: public TermIndexingStructure, SubstitutionTree
{
public:
  CLASS_NAME(TermSubstitutionTree);
  USE_ALLOCATOR(TermSubstitutionTree);

  TermSubstitutionTree(Shell::Options::UnificationWithAbstraction uwa, bool useC=false);

  void insert(TermList t, Literal* lit, Clause* cls) final override;
  void remove(TermList t, Literal* lit, Clause* cls) final override;

  bool generalizationExists(TermList t) final override;


  TermQueryResultIterator getUnifications(TermList t,
	  bool retrieveSubstitutions) final override;

  TermQueryResultIterator getUnificationsWithConstraints(TermList t,
          bool retrieveSubstitutions) final override;

  TermQueryResultIterator getGeneralizations(TermList t,
	  bool retrieveSubstitutions) final override;

  TermQueryResultIterator getInstances(TermList t,
	  bool retrieveSubstitutions) final override;

#if VDEBUG
  virtual void markTagged() final override { SubstitutionTree::markTagged();}
#endif

private:
  void handleTerm(TermList t, Literal* lit, Clause* cls, bool insert);

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

  virtual std::ostream& output(std::ostream& out) const final override;

  typedef SkipList<LeafData,LDComparator> LDSkipList;
  LDSkipList _vars;
};

};

#endif /* __TermSubstitutionTree__ */
