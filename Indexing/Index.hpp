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
#include "Debug/Output.hpp"

#include "Lib/Event.hpp"
#include "Kernel/Clause.hpp"
#include "Lib/Exception.hpp"
#include "Lib/VirtualIterator.hpp"
#include "Saturation/ClauseContainer.hpp"
#include "ResultSubstitution.hpp"
#include "Kernel/UnificationWithAbstraction.hpp"

#include "Lib/Allocator.hpp"

namespace Indexing
{
using namespace Kernel;
using namespace Lib;
using namespace Saturation;


struct LiteralClause 
{

  LiteralClause() {}
  using Key = Literal*;

  Key const& key() const
  { return literal; }


  LiteralClause(Clause* cls, Literal* literal)
    : clause(cls), literal(literal) {  }

  LiteralClause(Literal* lit, Clause* cl)
    : LiteralClause(cl, lit) {}

private:
  auto asTuple() const
  { return std::make_tuple(
      clause == nullptr, 
      clause == nullptr ? 0 : clause->number(), 
      literal == nullptr,
      literal == nullptr ? 0 : literal->getId()); }
public:

  IMPL_COMPARISONS_FROM_TUPLE(LiteralClause)

  Clause* clause;
  Literal* literal;
  TermList sort() { return key()->isEquality() ? SortHelper::getEqualityArgumentSort(key()) : TermList::empty();  };


  friend std::ostream& operator<<(std::ostream& out, LiteralClause const& self)
  { return out << "{ " << outputPtr(self.clause)
               << ", " << outputPtr(self.literal)
               << " }"; }

};

template<class Value>
class TermWithValue {
  TypedTermList _key;
  Value _value;
public:

  TermWithValue() {}

  TermWithValue(TypedTermList key, Value v)
    : _key(key)
    , _value(std::move(v))
  {}

  using Key = TypedTermList;
  Key const& key() const 
  { return _key; }

  TermList sort() const 
  { return SortHelper::getResultSort(_key.term()); }

  Value const& value() const 
  { return _value; }

private:
  auto asTuple() const
  { return std::tie(key(), value()); }
public:

  IMPL_COMPARISONS_FROM_TUPLE(TermWithValue)

  friend std::ostream& operator<<(std::ostream& out, TermWithValue const& self)
  { return out << "TermWithValue" << self.asTuple(); }
};

struct ClauseLiteralPair 
{

  ClauseLiteralPair() {}

  ClauseLiteralPair(Clause* c, Literal* l)
    : clause(c), literal(l) {}

protected:
  auto  asTuple() const
  { return std::make_tuple(
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

struct TermLiteralClause 
{

  Clause* clause;
  Literal* literal;
  TypedTermList term;


  using Key = TypedTermList;

  TermLiteralClause() : clause(nullptr), literal(nullptr), term() {}

  TermLiteralClause(TypedTermList t, Literal* l, Clause* c)
    : clause(c), literal(l), term(t) {}

  explicit TermLiteralClause(Term* t)
    : TermLiteralClause(TypedTermList(t), nullptr, nullptr)
  {}

  Key const& key() const { return term; }

private:
  auto  asTuple() const
  { return std::make_tuple(
      clause  == nullptr, clause  == nullptr ? 0 : clause->number(), 
      literal == nullptr, literal == nullptr ? 0 : literal->getId(), 
      term); }
public:

  IMPL_COMPARISONS_FROM_TUPLE(TermLiteralClause)

  friend std::ostream& operator<<(std::ostream& out, TermLiteralClause const& self)
  { return out << "TermLiteralClause("
               << self.term << ", "
               << outputPtr(self.literal)
               << outputPtr(self.clause)
               << ")"; }

};

/**
 * Class of objects which contain results of term queries.
 */
template<class Unifier, class Data>
struct QueryRes
{
  Unifier unifier;
  Data const* data;

  QueryRes() {}
  QueryRes(Unifier unifier, Data const* data) 
    : unifier(std::move(unifier))
    , data(std::move(data)) {}



  friend std::ostream& operator<<(std::ostream& out, QueryRes const& self)
  { 
    return out 
      << "{ data: " << self.data()
      << ", unifier: " << self.unifier
      << "}";
  }
};

template<class Unifier, class Data>
QueryRes<Unifier, Data> queryRes(Unifier unifier, Data const* d) 
{ return QueryRes<Unifier, Data>(std::move(unifier), std::move(d)); }

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

using TermQueryResult = QueryRes<ResultSubstitutionSP, TermLiteralClause>;
using SLQueryResult   = QueryRes<ResultSubstitutionSP, LiteralClause>;

using TermQueryResultIterator = VirtualIterator<TermQueryResult>;
using SLQueryResultIterator   = VirtualIterator<SLQueryResult>;
typedef VirtualIterator<ClauseSResQueryResult> ClauseSResResultIterator;
typedef VirtualIterator<FormulaQueryResult> FormulaQueryResultIterator;

class Index
{
public:

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

  virtual ClauseSResResultIterator getSubsumingOrSResolvingClauses(Clause* c, 
    bool subsumptionResolution)
  { NOT_IMPLEMENTED; };
};

};
#endif /*__Indexing_Index__*/
