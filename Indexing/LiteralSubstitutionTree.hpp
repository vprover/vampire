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
  LiteralSubstitutionTree();

  void insert(Literal* lit, Clause* cls);
  void remove(Literal* lit, Clause* cls);
  void handleLiteral(Literal* lit, Clause* cls, bool insert);

  SLQueryResultIterator getUnifications(Literal* lit,
	  bool complementary, bool retrieveSubstitutions);

  SLQueryResultIterator getGeneralizations(Literal* lit,
	  bool complementary, bool retrieveSubstitutions);

  SLQueryResultIterator getInstances(Literal* lit,
	  bool complementary, bool retrieveSubstitutions);

private:
  struct SLQueryResultFunctor;
  struct LDToSLQueryResultFn;
  struct PropositionalLDToSLQueryResultWithSubstFn;

  template<class Iterator>
  SLQueryResultIterator getResultIterator(Literal* lit,
	  bool complementary, bool retrieveSubstitutions);

  unsigned getRootNodeIndex(Literal* t, bool complementary=false);
};

};

#endif /* __LiteralSubstitutionTree__ */
