/**
 * @file LiteralSubstitutionTreeWithoutTop.hpp
 * Defines class LiteralSubstitutionTreeWithoutTop.
 *
 * @author Giles
 * TODO refactor to remove duplication with LiteralSubstitutionTree
 */


#ifndef __LiteralSubstitutionTreeWithoutTop__
#define __LiteralSubstitutionTreeWithoutTop__

#include "LiteralIndexingStructure.hpp"
#include "SubstitutionTree.hpp"

namespace Indexing {

class LiteralSubstitutionTreeWithoutTop
: public LiteralIndexingStructure, SubstitutionTree
{
public:
  CLASS_NAME(LiteralSubstitutionTreeWithoutTop);
  USE_ALLOCATOR(LiteralSubstitutionTreeWithoutTop);

  LiteralSubstitutionTreeWithoutTop();

  void insert(Literal* lit, Clause* cls);
  void remove(Literal* lit, Clause* cls);
  void handleLiteral(Literal* lit, Clause* cls, bool insert);

  SLQueryResultIterator getAll();

  SLQueryResultIterator getUnifications(Literal* lit,
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
	  bool complementary, bool retrieveSubstitutions);

  Node* _posRoot;
  Node* _negRoot;
};

};

#endif /* __LiteralSubstitutionTreeWithoutTop__ */
