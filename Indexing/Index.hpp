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

#include "Lib/Allocator.hpp"

namespace Indexing
{

using namespace Kernel;
using namespace Lib;
using namespace Saturation;


struct DefaultLiteralLeafData {
  DefaultLiteralLeafData() {}
  using Key = Literal*;

  Key const& key() const
  { return literal; }


  DefaultLiteralLeafData(Clause* cls, Literal* literal)
    : clause(cls), literal(literal) {  }

private:
  auto toTuple() const
  { return std::tie(clause, literal); }
public:

  // TODO shouldn't extraTerm be compared as well?
  friend bool operator==(DefaultLiteralLeafData const& l, DefaultLiteralLeafData const& r)
  { return l.toTuple() == r.toTuple(); }

  friend bool operator!=(DefaultLiteralLeafData const& l, DefaultLiteralLeafData const& r)
  { return !(l == r); }

  friend bool operator<(DefaultLiteralLeafData const& l, DefaultLiteralLeafData const& r)
  { return l.toTuple() < r.toTuple(); }

  friend bool operator> (DefaultLiteralLeafData const& l, DefaultLiteralLeafData const& r) { return r < l; }
  friend bool operator<=(DefaultLiteralLeafData const& l, DefaultLiteralLeafData const& r) { return l == r || l < r; }
  friend bool operator>=(DefaultLiteralLeafData const& l, DefaultLiteralLeafData const& r) { return l == r || l > r; }

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


struct DefaultLeafData {
  using Key = TermList;

  DefaultLeafData() {}

  // DefaultLeafData(Clause* cls, Literal* literal, TermList term, TermList extraTerm)
  //   : clause(cls), literal(literal), term(term), extraTerm(extraTerm) {}

  DefaultLeafData(TermList t, Literal* l, Clause* c, TermList extraTerm)
    : clause(c), literal(l), term(t), extraTerm(extraTerm) {}

  DefaultLeafData(TermList t, Literal* l, Clause* c)
    : clause(c), literal(l), term(t) { extraTerm.makeEmpty(); }

  // DefaultLeafData(Clause* cls, Literal* literal)
  //   : clause(cls), literal(literal) { term.makeEmpty(); extraTerm.makeEmpty(); }

  explicit DefaultLeafData(Term* term)
    : clause(nullptr), literal(nullptr),  term(TermList(term))
  { extraTerm.makeEmpty(); }

  // TODO maybe make sort an argument and not recompute it here
  TermList sort() const
  {
    return SortHelper::getTermSort(term, literal);
  }

  Key const& key() const 
  { return term; }

private:
  auto toTuple() const
  { return std::tie(clause, literal, term, extraTerm); }
public:

  // TODO shouldn't extraTerm be compared as well?
  friend bool operator==(DefaultLeafData const& l, DefaultLeafData const& r)
  { return l.toTuple() == r.toTuple(); }

  friend bool operator!=(DefaultLeafData const& l, DefaultLeafData const& r)
  { return !(l == r); }

  friend bool operator<(DefaultLeafData const& l, DefaultLeafData const& r)
  { return l.toTuple() < r.toTuple(); }

  friend bool operator> (DefaultLeafData const& l, DefaultLeafData const& r) { return r < l; }
  friend bool operator<=(DefaultLeafData const& l, DefaultLeafData const& r) { return l == r || l < r; }
  friend bool operator>=(DefaultLeafData const& l, DefaultLeafData const& r) { return l == r || l > r; }

  Clause* clause;
  Literal* literal;
  TermList term;
  // In some higher-order use cases, we want to store a different term 
  // in the leaf to the indexed term. extraTerm is used for this purpose.
  // In all other situations it is empty
  TermList extraTerm;

  // vstring toString() {
  //   vstring ret = "LD " + literal->toString();// + " in " + clause->literalsOnlyToString();
  //   if(!term.isEmpty()){ ret += " with " +term.toString(); }
  //   return ret;
  // }

  friend std::ostream& operator<<(std::ostream& out, DefaultLeafData const& self)
  { 
    out << "DefaultLeafData("
        << self.term << ", ";
    if (self.literal) out << *self.literal;
    else              out << "null";
    out << ", ";
    if (self.clause) out << *self.clause;
    else             out << "null";
    out << ", " << self.extraTerm;
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
