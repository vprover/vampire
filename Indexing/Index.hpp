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
 * @file Indexing/Index.hpp
 * Defines abstract Index class and some other auxiliary classes.
 */

#ifndef __Indexing_Index__
#define __Indexing_Index__

#include "Forwards.hpp"

#include "Lib/Event.hpp"
#include "Lib/Exception.hpp"
#include "Lib/VirtualIterator.hpp"
#include "Saturation/ClauseContainer.hpp"
#include "ResultSubstitution.hpp"

#include "Lib/Allocator.hpp"

namespace Indexing
{

using namespace Kernel;
using namespace Lib;
using namespace Saturation;


/**
 * Class of objects which contain results of single literal queries.
 */
struct SLQueryResult
{
  SLQueryResult() {}
  SLQueryResult(Literal* l, Clause* c, ResultSubstitutionSP s)
  : literal(l), clause(c), substitution(s) {}
  SLQueryResult(Literal* l, Clause* c)
  : literal(l), clause(c) {}
  SLQueryResult(Literal* l, Clause* c, ResultSubstitutionSP s,UnificationConstraintStackSP con)
  : literal(l), clause(c), substitution(s), constraints(con) {}


  Literal* literal;
  Clause* clause;
  ResultSubstitutionSP substitution;
  UnificationConstraintStackSP constraints;

  struct ClauseExtractFn
  {
    Clause* operator()(const SLQueryResult& res)
    {
      return res.clause;
    }
  };
};

/**
 * Class of objects which contain results of term queries.
 */
struct TermQueryResult
{
  TermQueryResult() : literal(nullptr), clause(nullptr) {}
  TermQueryResult(TermList t, Literal* l, Clause* c, ResultSubstitutionSP s)
  : term(t), literal(l), clause(c), substitution(s) {}
  TermQueryResult(TermList t, Literal* l, Clause* c, ResultSubstitutionSP s, bool b)
  : term(t), literal(l), clause(c), substitution(s), isTypeSub(b) {}
  TermQueryResult(TermList t, Literal* l, Clause* c)
  : term(t), literal(l), clause(c) {}
  TermQueryResult(TermList t, Literal* l, Clause* c, ResultSubstitutionSP s,UnificationConstraintStackSP con)
  : term(t), literal(l), clause(c), substitution(s), constraints(con) {}
  TermQueryResult(TermList t, Literal* l, Clause* c, ResultSubstitutionSP s,UnificationConstraintStackSP con, bool b)
  : term(t), literal(l), clause(c), substitution(s), constraints(con), isTypeSub(b) {}

  TermList term;
  Literal* literal;
  Clause* clause;
  ResultSubstitutionSP substitution;
  UnificationConstraintStackSP constraints;
  bool isTypeSub = false; //true if the substitution only unifies the types of the terms
};

struct ClauseSResQueryResult
{
  ClauseSResQueryResult() {}
  ClauseSResQueryResult(Clause* c)
  : clause(c), resolved(false) {}
  ClauseSResQueryResult(Clause* c, unsigned rqlIndex)
  : clause(c), resolved(true), resolvedQueryLiteralIndex(rqlIndex) {}
  
  Clause* clause;
  bool resolved;
  unsigned resolvedQueryLiteralIndex;
};

struct FormulaQueryResult
{
  FormulaQueryResult() {}
  FormulaQueryResult(FormulaUnit* unit, Formula* f, ResultSubstitutionSP s=ResultSubstitutionSP())
  : unit(unit), formula(f), substitution(s) {}

  FormulaUnit* unit;
  Formula* formula;
  ResultSubstitutionSP substitution;
};

typedef VirtualIterator<SLQueryResult> SLQueryResultIterator;
typedef VirtualIterator<TermQueryResult> TermQueryResultIterator;
typedef VirtualIterator<ClauseSResQueryResult> ClauseSResResultIterator;
typedef VirtualIterator<FormulaQueryResult> FormulaQueryResultIterator;

class Index
{
public:
  CLASS_NAME(Index);
  USE_ALLOCATOR(Index);

  virtual ~Index();

  void attachContainer(ClauseContainer* cc);
protected:
  Index() {}

  void onAddedToContainer(Clause* c)
  { handleClause(c, true); }
  void onRemovedFromContainer(Clause* c)
  { handleClause(c, false); }

  virtual void handleClause(Clause* c, bool adding) {}

  //TODO: postponing index modifications during iteration (methods isBeingIterated() etc...)

private:
  SubscriptionData _addedSD;
  SubscriptionData _removedSD;
};



class ClauseSubsumptionIndex
: public Index
{
public:
  CLASS_NAME(ClauseSubsumptionIndex);
  USE_ALLOCATOR(ClauseSubsumptionIndex);

  virtual ClauseSResResultIterator getSubsumingOrSResolvingClauses(Clause* c, 
    bool subsumptionResolution)
  { NOT_IMPLEMENTED; };
};

};
#endif /*__Indexing_Index__*/
