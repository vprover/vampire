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
#include "Kernel/Clause.hpp"
#include "Lib/Exception.hpp"
#include "Lib/VirtualIterator.hpp"
#include "Saturation/ClauseContainer.hpp"
#include "ResultSubstitution.hpp"
#include "Kernel/SortHelper.hpp"
#include "Lib/Reflection.hpp"

#include "Lib/Allocator.hpp"

namespace Indexing
{

using namespace Kernel;
using namespace Lib;
using namespace Saturation;


struct DefaultLiteralLeafData 
{
  CLASS_NAME(DefaultLiteralLeafData);

  DefaultLiteralLeafData() {}
  using Key = Literal*;

  Key const& key() const
  { return literal; }


  DefaultLiteralLeafData(Clause* cls, Literal* literal)
    : clause(cls), literal(literal) {  }

private:
  auto asTuple() const
  { return make_tuple(
      clause == nullptr, 
      clause == nullptr ? 0 : clause->number(), 
      literal == nullptr,
      literal == nullptr ? 0 : literal->getId()); }
public:

  IMPL_COMPARISONS_FROM_TUPLE(DefaultLiteralLeafData)

  Clause* clause;
  Literal* literal;

  friend std::ostream& operator<<(std::ostream& out, DefaultLiteralLeafData const& self)
  { 
    out << "DefaultLiteralLeafData(";
    if (self.literal) out << *self.literal;
    else              out << "null";
    out << ", ";
    if (self.clause) out << *self.clause;
    else             out << "null";
    out << ")";
    return out;
  }

};

template<class Value>
class TermIndexData {
  TermList _key;
  TermList _sort;
  Value _value;
public:
  CLASS_NAME(TermIndexData);

  TermIndexData() {}

  TermIndexData(Term* key, Value v)
    : _key(TermList(key))
    , _sort(SortHelper::getResultSort(key))
    , _value(std::move(v)) {}

  TermList const& sort() const
  { return _sort; }

  TermList const& key() const 
  { return _key; }

  Value const& value() const 
  { return _value; }

private:
  auto asTuple() const
  { return std::tie(key(), sort(), value()); }
public:

  IMPL_COMPARISONS_FROM_TUPLE(TermIndexData)

  friend std::ostream& operator<<(std::ostream& out, TermIndexData const& self)
  { return out << "TermIndexData" << self.asTuple(); }
};

struct ClauseLiteralPair 
{
  CLASS_NAME(ClauseLiteralPair);

  ClauseLiteralPair() {}

  ClauseLiteralPair(Clause* c, Literal* l)
    : clause(c), literal(l) {}

protected:
  auto  asTuple() const
  { return make_tuple(
      clause == nullptr, 
      clause == nullptr ? 0 : clause->number(), 
      literal == nullptr,
      literal == nullptr ? 0 : literal->getId()); }
public:

  IMPL_COMPARISONS_FROM_TUPLE(ClauseLiteralPair)

  Clause* clause;
  Literal* literal;

  friend std::ostream& operator<<(std::ostream& out, ClauseLiteralPair const& self)
  { 
    out << "(";
    if (self.literal) out << *self.literal;
    else              out << "null";
    out << ", ";
    if (self.clause) out << *self.clause;
    else             out << "null";
    out << ")";
    return out;
  }
};

struct DefaultTermLeafData 
{
  CLASS_NAME(DefaultTermLeafData);

  Clause* clause;
  Literal* literal;
  TermList term;


  using Key = TermList;

  DefaultTermLeafData() {}

  DefaultTermLeafData(TermList t, Literal* l, Clause* c)
    : clause(c), literal(l), term(t) {}

  explicit DefaultTermLeafData(Term* term)
    : clause(nullptr), literal(nullptr),  term(TermList(term))
  {}

  // TODO maybe make sort an argument and not recompute it here
  TermList sort() const
  { return SortHelper::getTermSort(term, literal); }

  Key const& key() const 
  { return term; }

private:
  auto  asTuple() const
  { return make_tuple(
      clause == nullptr, 
      clause == nullptr ? 0 : clause->number(), 
      literal == nullptr,
      literal == nullptr ? 0 : literal->getId(), 
      term); }
public:

  IMPL_COMPARISONS_FROM_TUPLE(DefaultTermLeafData)

  friend std::ostream& operator<<(std::ostream& out, DefaultTermLeafData const& self)
  { 
    out << "DefaultTermLeafData("
        << self.term << ", ";
    if (self.literal) out << *self.literal;
    else              out << "null";
    out << ", ";
    if (self.clause) out << *self.clause;
    else             out << "null";
    out << ")";
    return out;
  }

};


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
template<class Data>
struct TermQueryResult : public Data
{
  CLASS_NAME(TermQueryResult)

  TermQueryResult() {}

  TermQueryResult(Data d, ResultSubstitutionSP s)
    : Data(std::move(d)), substitution(s) {}

  TermQueryResult(Data d, ResultSubstitutionSP s, bool b)
    : Data(std::move(d)), substitution(s), isTypeSub(b) {}

  TermQueryResult(Data d)
    : Data(std::move(d)) {}

  TermQueryResult(Data d, ResultSubstitutionSP s,UnificationConstraintStackSP con) 
    : Data(std::move(d)), substitution(s), constraints(con) {}

  TermQueryResult(Data d, ResultSubstitutionSP s,UnificationConstraintStackSP con, bool b)
    : Data(std::move(d)), substitution(s), constraints(con), isTypeSub(b) {}


  Data const& data() const
  { return *this; }

  ResultSubstitutionSP substitution;
  UnificationConstraintStackSP constraints;
  bool isTypeSub = false; //true if the substitution only unifies the types of the terms
                          //
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
template<class Data>
using TermQueryResultIterator = VirtualIterator<TermQueryResult<Data>> ;
typedef VirtualIterator<ClauseSResQueryResult> ClauseSResResultIterator;
typedef VirtualIterator<FormulaQueryResult> FormulaQueryResultIterator;

class Index
{
public:
  CLASS_NAME(Index);

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

  virtual ClauseSResResultIterator getSubsumingOrSResolvingClauses(Clause* c, 
    bool subsumptionResolution)
  { NOT_IMPLEMENTED; };
};

};
#endif /*__Indexing_Index__*/
