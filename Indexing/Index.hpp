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

  DefaultLiteralLeafData(Literal* lit, Clause* cl)
    : DefaultLiteralLeafData(cl, lit) {}

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
  TermList sort() { return key()->isEquality() ? SortHelper::getEqualityArgumentSort(key()) : TermList::empty();  };


  friend std::ostream& operator<<(std::ostream& out, DefaultLiteralLeafData const& self)
  { return out << "{ " << outputPtr(self.clause)
               << ", " << outputPtr(self.literal)
               << " }"; }

};

template<class Value>
class TermIndexData {
  TermList _key;
  // TODO rename to _extra (?)
  Value _value;
public:
  CLASS_NAME(TermIndexData);

  TermIndexData() {}

  TermIndexData(Term* key, Value v)
    : _key(TermList(key))
    , _value(std::move(v))
  {}

  TermList const& key() const 
  { return _key; }

  TermList sort() const 
  { return SortHelper::getResultSort(_key.term()); }

  Value const& value() const 
  { return _value; }

private:
  auto asTuple() const
  { return std::tie(key(), value()); }
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

struct TermLiteralClause 
{
  CLASS_NAME(TermLiteralClause);

  Clause* clause;
  Literal* literal;
  TermList term;
  TermList _sort;


  using Key = TermList;

  TermLiteralClause() {}

  TermLiteralClause(TypedTermList t, Literal* l, Clause* c)
    : clause(c), literal(l), term(t), _sort(t.sort()) {}

  TermLiteralClause(TermList t, Literal* l, Clause* c)
    : clause(c), literal(l), term(t), _sort(TermList::empty()) {}

  explicit TermLiteralClause(Term* t)
    : TermLiteralClause(TypedTermList(t), nullptr, nullptr)
  {}

  Key const& key() const { return term; }
  TermList sort() const { return _sort; }

private:
  auto  asTuple() const
  { return make_tuple(
      clause  == nullptr, clause  == nullptr ? 0 : clause->number(), 
      literal == nullptr, literal == nullptr ? 0 : literal->getId(), 
      term,
      _sort); }
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

using TermQueryResult = QueryRes<ResultSubstitutionSP ,   TermLiteralClause>;
using SLQueryResult   = QueryRes<ResultSubstitutionSP, DefaultLiteralLeafData>;

using TermQueryResultIterator = VirtualIterator<TermQueryResult>;
using SLQueryResultIterator   = VirtualIterator<SLQueryResult>;
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
