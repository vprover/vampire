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

class CodeTreeTIS : public TermIndexingStructure<TermLiteralClause>
{
public:
  /* INFO: we ignore unifying the sort of the keys here */
  virtual void handle(TermLiteralClause data, bool insert) final override
  { if (insert) { _insert(data.term, data.literal, data.clause); }
    else        { _remove(data.term, data.literal, data.clause); } }

  VirtualIterator<QueryRes<ResultSubstitutionSP, TermLiteralClause>> getGeneralizations(TypedTermList t, bool retrieveSubstitutions = true) final override;
  // TODO use TypedTermList here too
  bool generalizationExists(TermList t) final override;
  // TODO: get rid of NOT_IMPLEMENTED
  VirtualIterator<QueryRes<AbstractingUnifier*, TermLiteralClause>> getUwa(TypedTermList t, Options::UnificationWithAbstraction, bool fixedPointIteration) override { NOT_IMPLEMENTED; }

  virtual void output(std::ostream& out) const final override { out << "CodeTree"; }

private:
  void _insert(TypedTermList t, Literal* lit, Clause* cls);
  void _remove(TypedTermList t, Literal* lit, Clause* cls);

  class ResultIterator;

  TermCodeTree _ct;
};

class CodeTreeSubsumptionIndex
: public Index
{
public:
protected:
  void handleClause(Clause* c, bool adding) override;
private:

  ClauseCodeTree _ct;
};

};
#endif /*__CodeTreeInterfaces__*/
