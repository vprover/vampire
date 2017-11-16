
/*
 * File LiteralIndexingStructure.hpp.
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
 * @file LiteralIndexingStructure.hpp
 * Defines class LiteralIndexingStructure.
 */


#ifndef __LiteralIndexingStructure__
#define __LiteralIndexingStructure__

#include "Forwards.hpp"
#include "Index.hpp"

namespace Indexing {

class LiteralIndexingStructure {
public:
  virtual ~LiteralIndexingStructure() {}

  virtual void insert(Literal* lit, Clause* cls) = 0;
  virtual void remove(Literal* lit, Clause* cls) = 0;

  virtual SLQueryResultIterator getAll() { NOT_IMPLEMENTED; }
  virtual SLQueryResultIterator getUnifications(Literal* lit,
	  bool complementary, bool retrieveSubstitutions = true) { NOT_IMPLEMENTED; }
  virtual SLQueryResultIterator getUnificationsWithConstraints(Literal* lit,
          bool complementary, bool retrieveSubstitutions = true) { NOT_IMPLEMENTED; }
  virtual SLQueryResultIterator getGeneralizations(Literal* lit,
	  bool complementary, bool retrieveSubstitutions = true) { NOT_IMPLEMENTED; }
  virtual SLQueryResultIterator getInstances(Literal* lit,
	  bool complementary, bool retrieveSubstitutions = true) { NOT_IMPLEMENTED; }
  virtual SLQueryResultIterator getVariants(Literal* lit,
	  bool complementary, bool retrieveSubstitutions = true) { NOT_IMPLEMENTED; }

  virtual size_t getUnificationCount(Literal* lit, bool complementary)
  {
    CALL("LiteralIndexingStructure::getUnificationCount");
    return countIteratorElements(getUnifications(lit, complementary, false));
  }

#if VDEBUG
  virtual vstring toString() { return "<not supported>"; }
  virtual void markTagged() = 0;
#endif

};

};

#endif /* __LiteralIndexingStructure__ */
