/**
 * @file TermSubstitutionTree.hpp
 * Defines class TermSubstitutionTree.
 */


#ifndef __TermSubstitutionTree__
#define __TermSubstitutionTree__


#include "../Lib/SkipList.hpp"

#include "Index.hpp"
#include "TermIndexingStructure.hpp"
#include "SubstitutionTree.hpp"

namespace Indexing {

class TermSubstitutionTree
: public TermIndexingStructure, SubstitutionTree
{
public:
  TermSubstitutionTree();

  void insert(TermList t, Literal* lit, Clause* cls);
  void remove(TermList t, Literal* lit, Clause* cls);


  TermQueryResultIterator getUnifications(TermList t,
	  bool retrieveSubstitutions);

  TermQueryResultIterator getGeneralizations(TermList t,
	  bool retrieveSubstitutions);

  TermQueryResultIterator getInstances(TermList t,
	  bool retrieveSubstitutions);

private:
  void handleTerm(TermList t, Literal* lit, Clause* cls, bool insert);

  class TermQueryResultFn;

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

  TermQueryResultIterator getAllUnifyingIterator(TermList var,
	  bool retrieveSubstitutions);

  inline
  unsigned getRootNodeIndex(Term* t)
  {
    return t->functor();
  }


  typedef SkipList<LeafData,LDComparator> LDSkipList;
  LDSkipList _vars;
};

};

#endif /* __TermSubstitutionTree__ */
