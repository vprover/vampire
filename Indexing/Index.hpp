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
#include "Lib/Output.hpp"

#include "Lib/Event.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TypedTermList.hpp"
#include "Saturation/ClauseContainer.hpp"
#include "Kernel/Clause.hpp"

/**
 * Indices are parametrized by a LeafData, i.e. the bit of data you want to store in the index.
 * Each leaf data must have a key to store at the leave. The Key can currently be either a Literal* or a TypedTermList.
 * A LeafData must have a function  `<Key> key() const;` returns the key, and must have comparison operators (<=,<,>=,>,!=,==) implemented.
 * See e.g. TermLiteralClause below for examples.
 */
namespace Indexing
{
using namespace Kernel;
using namespace Lib;
using namespace Saturation;

struct LiteralClause 
{
  Literal* const& key() const
  { return literal; }

private:
  std::tuple<unsigned,unsigned> asTuple() const
  { return std::make_tuple(clause->number(), literal->getId()); }
public:

  IMPL_COMPARISONS_FROM_TUPLE(LiteralClause)

  Literal* literal = nullptr;
  Clause* clause = nullptr;

  friend std::ostream& operator<<(std::ostream& out, LiteralClause const& self)
  { return out << "{ " << Output::ptr(self.clause) << ", " << Output::ptr(self.literal) << " }"; }
};

template<class Key, class Value>
struct KeyWithValue {
  Key _key;
  Value value;

  KeyWithValue() {}

  KeyWithValue(Key key, Value v)
    : _key(key)
    , value(std::move(v))
  {}

  auto const& key() const { return _key; }

  std::tuple<const Key &,const Value &> asTuple() const
  { return std::tie(_key, value); }

  IMPL_COMPARISONS_FROM_TUPLE(KeyWithValue)

  friend std::ostream& operator<<(std::ostream& out, KeyWithValue const& self)
  { return out << self.asTuple(); }
};

template<class Key>
class KeyWithoutValue : public KeyWithValue<Key, std::tuple<>>
{
public:
  KeyWithoutValue(Key k) 
    : KeyWithValue<Key, std::tuple<>>(k, std::make_tuple())
  { }
};

template<class Value>
using TermWithValue = KeyWithValue<TypedTermList,Value>;
using TermWithoutValue = KeyWithoutValue<TypedTermList>;

template<class Value>
using LiteralWithValue = KeyWithValue<Literal*,Value>;

struct TermLiteralClause 
{
  TypedTermList term;
  Literal* literal = nullptr;
  Clause* clause = nullptr;

  TypedTermList key() const { return term; }

  auto  asTuple() const
  { return std::make_tuple(clause->number(), literal->getId(), term); }

  IMPL_COMPARISONS_FROM_TUPLE(TermLiteralClause)

  friend std::ostream& operator<<(std::ostream& out, TermLiteralClause const& self)
  { return out << "("
               << self.term << ", "
               << self.literal
               << Output::ptr(self.clause)
               << ")"; }
};

template<class T>
struct is_indexed_data_normalized
{ static constexpr bool value = false; };

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

class Index
{
public:
  virtual ~Index();

  void attachContainer(ClauseContainer* cc);
protected:
  void onAddedToContainer(Clause* c)
  { handleClause(c, true); }
  void onRemovedFromContainer(Clause* c)
  { handleClause(c, false); }

  virtual void handleClause(Clause* c, bool adding) = 0;

  //TODO: postponing index modifications during iteration (methods isBeingIterated() etc...)

private:
  SubscriptionData _addedSD;
  SubscriptionData _removedSD;
};

};
#endif /*__Indexing_Index__*/
