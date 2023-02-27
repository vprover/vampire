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

class CodeTreeTIS : public TermIndexingStructure<DefaultTermLeafData>
{
public:

  CLASS_NAME(CodeTreeTIS);
  USE_ALLOCATOR(CodeTreeTIS);

  virtual void handle(DefaultTermLeafData data, bool insert) final override
  { if (insert) { _insert(data.term, data.literal, data.clause); }
    else        { _remove(data.term, data.literal, data.clause); } }

  TermQueryResultIterator getGeneralizations(TermList t, bool retrieveSubstitutions = true) final override;
  bool generalizationExists(TermList t) final override;
  // TODO: get rid of NOT_IMPLEMENTED
  VirtualIterator<QueryRes<AbstractingUnifier*, DefaultTermLeafData>> getUwa(TypedTermList t, Options::UnificationWithAbstraction, bool fixedPointIteration) override { NOT_IMPLEMENTED; }

  virtual void output(std::ostream& out) const final override { out << "CodeTree"; }

private:
  void _insert(TermList t, Literal* lit, Clause* cls);
  void _remove(TermList t, Literal* lit, Clause* cls);

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
