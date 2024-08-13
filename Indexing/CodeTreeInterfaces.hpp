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


/**
 * Term indexing structure using code trees to retrieve generalizations
 */

template<class Data>
class CodeTreeTIS : public TermIndexingStructure<Data>
{
public:
  /* INFO: we ignore unifying the sort of the keys here */
  void handle(Data data, bool insert) final override
  {
    if (insert) {
      auto ti = new Data(std::move(data));
      _ct.insert(ti);
    } else {
      _ct.remove(data);
    }
  }

  Lib::VirtualIterator<QueryRes<ResultSubstitutionSP, Data>> getGeneralizations(TypedTermList t, bool retrieveSubstitutions = true) final override;
  // TODO use TypedTermList here too
  bool generalizationExists(TermList t) final override;
  // TODO: get rid of NOT_IMPLEMENTED
  Lib::VirtualIterator<QueryRes<AbstractingUnifier*, Data>> getUwa(TypedTermList t, Options::UnificationWithAbstraction, bool fixedPointIteration) override { NOT_IMPLEMENTED; }

  virtual void output(std::ostream& out) const final override { out << _ct; }

private:
  class ResultIterator;

  TermCodeTree<Data> _ct;
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
