/**
 * @file LiteralIndexingStructure.hpp
 * Defines class LiteralIndexingStructure.
 */


#ifndef __LiteralIndexingStructure__
#define __LiteralIndexingStructure__

#include "../Forwards.hpp"
#include "Index.hpp"

namespace Indexing {

class LiteralIndexingStructure {
public:
  virtual ~LiteralIndexingStructure() {}

  virtual void insert(Literal* lit, Clause* cls) = 0;
  virtual void remove(Literal* lit, Clause* cls) = 0;

  virtual SLQueryResultIterator getAll() = 0;
  virtual SLQueryResultIterator getUnifications(Literal* lit,
	  bool complementary, bool retrieveSubstitutions = true) = 0;
  virtual SLQueryResultIterator getGeneralizations(Literal* lit,
	  bool complementary, bool retrieveSubstitutions = true) = 0;
  virtual SLQueryResultIterator getInstances(Literal* lit,
	  bool complementary, bool retrieveSubstitutions = true) = 0;
  virtual SLQueryResultIterator getVariants(Literal* lit,
	  bool complementary, bool retrieveSubstitutions = true) = 0;
};

};

#endif /* __LiteralIndexingStructure__ */
