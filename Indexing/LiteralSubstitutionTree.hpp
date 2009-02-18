/**
 * @file LiteralSubstitutionTree.hpp
 * Defines class LiteralSubstitutionTree.
 */


#ifndef __LiteralSubstitutionTree__
#define __LiteralSubstitutionTree__

#if COMPIT_GENERATOR

#if COMPIT_VERSION==2
#include "../Test/Compit2Output.hpp"
#else
#include "../Test/CompitOutput.hpp"
#endif

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
#if COMPIT_VERSION==2
      Compit2Output::print(Compit2Output::INSERT, norm.apply(lit));
#else
      CompitOutput::print(CompitOutput::INSERT, norm.apply(lit));
#endif
    }
  }
  void remove(Literal* lit, Clause* cls)
  {
    LiteralSubstitutionTree::insert(lit,cls);
    if(!lit->commutative()) {
      Renaming norm;
      norm.normalizeVariables(lit);
#if COMPIT_VERSION==2
      Compit2Output::print(Compit2Output::DELETE, norm.apply(lit));
#else
      CompitOutput::print(CompitOutput::DELETE, norm.apply(lit));
#endif
    }
  }

  SLQueryResultIterator getUnifications(Literal* lit, bool complementary, bool retrieveSubstitutions)
  {
    SLQueryResultIterator res=LiteralSubstitutionTree::getUnifications(lit,
	complementary, retrieveSubstitutions);
    if(!lit->commutative()) {
      Renaming norm;
      norm.normalizeVariables(lit);
#if COMPIT_VERSION==2
      unsigned count=0;
      while(res.hasNext()) {
	count++;
	res.next();
      }
      if(count) {
	res=LiteralSubstitutionTree::getUnifications(lit,complementary, retrieveSubstitutions);
      }
      Compit2Output::print(Compit2Output::QUERY, norm.apply(lit), count, complementary);
#else
      if(res.hasNext()) {
	CompitOutput::print(CompitOutput::SUCCESSFUL_QUERY, norm.apply(lit), complementary);
      } else {
	CompitOutput::print(CompitOutput::UNSUCCESSFUL_QUERY, norm.apply(lit), complementary);
      }
#endif
    }
    return res;
  }

};

#endif

};

#endif /* __LiteralSubstitutionTree__ */
