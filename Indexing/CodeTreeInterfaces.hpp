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
 * @file CodeTreeInterfaces.hpp
 * Defines classes of indexing structures that use code trees.
 */

#ifndef __CodeTreeInterfaces__
#define __CodeTreeInterfaces__

#include "Forwards.hpp"

#include "TermCodeTree.hpp"
#include "ClauseCodeTree.hpp"

#include "Index.hpp"
#include "TermIndexingStructure.hpp"
#include "LiteralIndexingStructure.hpp"

#include "Lib/Allocator.hpp"

namespace Indexing
{

using namespace Kernel;
using namespace Lib;


/**
 * Term indexing structure using code trees to retrieve generalizations
 */

class CodeTreeTIS : public TermIndexingStructure
{
public:
  CLASS_NAME(CodeTreeTIS);
  USE_ALLOCATOR(CodeTreeTIS);

  void insert(TermList t, Literal* lit, Clause* cls);
  void remove(TermList t, Literal* lit, Clause* cls);

  TermQueryResultIterator getGeneralizations(TermList t, bool retrieveSubstitutions = true);
  bool generalizationExists(TermList t);

#if VDEBUG
  virtual void markTagged(){ NOT_IMPLEMENTED; } 
#endif

private:
  class ResultIterator;

  TermCodeTree _ct;
};
/*
class CodeTreeLIS : public LiteralIndexingStructure
{
public:
  void insert(Literal* lit, Clause* cls);
  void remove(Literal* lit, Clause* cls);

  SLQueryResultIterator getGeneralizations(Literal* lit,
	  bool complementary, bool retrieveSubstitutions = true);
private:
  struct LiteralInfo;
  class ResultIterator;

  TermCodeTree _ct;
};
*/

class CodeTreeSubsumptionIndex
: public ClauseSubsumptionIndex
{
public:
  CLASS_NAME(CodeTreeSubsumptionIndex);
  USE_ALLOCATOR(CodeTreeSubsumptionIndex);

  ClauseSResResultIterator getSubsumingOrSResolvingClauses(Clause* c, bool subsumptionResolution);
protected:
  //overrides Index::handleClause
  void handleClause(Clause* c, bool adding);
private:
  class ClauseSResIterator;

  ClauseCodeTree _ct;
};

};
#endif /*__CodeTreeInterfaces__*/
