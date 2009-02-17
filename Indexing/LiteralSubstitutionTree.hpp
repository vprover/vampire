/**
 * @file LiteralSubstitutionTree.hpp
 * Defines class LiteralSubstitutionTree.
 */


#ifndef __LiteralSubstitutionTree__
#define __LiteralSubstitutionTree__

#if COMPIT_GENERATOR
#include "../Test/CompitOutput.hpp"
#endif

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

#if COMPIT_GENERATOR

using namespace Test;

class CompitUnificationRecordingLiteralSubstitutionTree
: public LiteralSubstitutionTree
{
  void insert(Literal* lit, Clause* cls)
  {
    LiteralSubstitutionTree::insert(lit,cls);
    if(!lit->commutative()) {
      Renaming norm;
      norm.normalizeVariables(lit);
      CompitOutput::print(CompitOutput::INSERT, norm.apply(lit));
    }
  }
  void remove(Literal* lit, Clause* cls)
  {
    LiteralSubstitutionTree::insert(lit,cls);
    if(!lit->commutative()) {
      Renaming norm;
      norm.normalizeVariables(lit);
      CompitOutput::print(CompitOutput::DELETE, norm.apply(lit));
    }
  }

  SLQueryResultIterator getUnifications(Literal* lit, bool complementary, bool retrieveSubstitutions)
  {
    SLQueryResultIterator res=LiteralSubstitutionTree::getUnifications(lit,
	    complementary, retrieveSubstitutions);
    if(!lit->commutative()) {
      Renaming norm;
      norm.normalizeVariables(lit);
      if(res.hasNext()) {
	CompitOutput::print(CompitOutput::SUCCESSFUL_QUERY, norm.apply(lit), complementary);
      } else {
	CompitOutput::print(CompitOutput::UNSUCCESSFUL_QUERY, norm.apply(lit), complementary);
      }
    }
    return res;
  }

};

#endif

};

#endif /* __LiteralSubstitutionTree__ */
