/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#ifndef __FingerprintIndex__
#define __FingerprintIndex__

#include "Lib/Array.hpp"
#include "Lib/Stack.hpp"
#include "Lib/STL.hpp"
#include <array>
#include "Indexing/TermIndexingStructure.hpp"
#include "Indexing/LiteralIndexingStructure.hpp"


namespace Indexing {
class FingerprintIndex {
public:
  CLASS_NAME(FingerprintIndex);
  USE_ALLOCATOR(FingerprintIndex);

  static const unsigned FINGERPRINT_SIZE = 6;
  static std::array<signed, FINGERPRINT_SIZE> fingerprint(Term* ts, bool complementary = false);
  FingerprintIndex();
  unsigned getBucket(Term* ts);
  void getUnifications(Stack<unsigned> &results, Term* ts, bool complementary = false);
  void getGeneralizations(Stack<unsigned> &results, Term* ts);
  void getInstances(Stack<unsigned> &results, Term* ts);

private:
  vmap<std::pair<unsigned, signed>, unsigned> _edges;
  unsigned _fresh_node;
  unsigned _fresh_bucket;
}; // class FingerprintIndex

// forward declaration
class TermFingerprintIndex;
class LiteralFingerprintIndex;

struct LitEntry {
  Clause *cls;
  Literal *lit;
  bool operator==(const LitEntry &other) const;
};

struct TermEntry {
  Clause *cls;
  Literal *lit;
  TermList term;
  bool operator==(const TermEntry &other) const;
};

template<class Entry, class Index> 
class EntryIterator // template definition
{ 
public:
  EntryIterator(
    const Index &index,
    Stack<unsigned> &&buckets
  );
  DECL_ELEMENT_TYPE(Entry);
  bool hasNext();
  void nextBucket();
  OWN_ELEMENT_TYPE next();
private:
  const Index &_index;
  Stack<unsigned> _buckets;
  typename vvector<Entry>::const_iterator _entry;
  typename vvector<Entry>::const_iterator _end;
};


using LitEntryIterator = EntryIterator<LitEntry, LiteralFingerprintIndex>;
using TermEntryIterator = EntryIterator<TermEntry, TermFingerprintIndex>;

class LiteralFingerprintIndex final : public LiteralIndexingStructure {
public:

  void insert(Literal* lit, Clause* cls) override;
  void remove(Literal* lit, Clause* cls) override;

  LiteralFingerprintIndex(vstring name) : _name(name) {}

  SLQueryResultIterator getUnifications(Literal* lit,
    bool complementary, bool retrieveSubstitutions) override;

  vstring name() { return _name; }

#if VDEBUG
  void markTagged() override {};
#endif
private: 

  class SLQRIterator {
  public:
    SLQRIterator(LitEntryIterator  results, Literal* lit);
    DECL_ELEMENT_TYPE(SLQueryResult);
    bool hasNext();
    OWN_ELEMENT_TYPE next();
    virtual bool prepareSubst() = 0;
  protected:
    LitEntryIterator _it;
    Literal* _query;
    RobSubstitutionSP _subst;
    SLQueryResult _next;
    bool _hasNext;
  };

  class UnificationIterator final : public SLQRIterator {
  public:
    using SLQRIterator::SLQRIterator;
    bool prepareSubst() override;
  };

  friend class EntryIterator<LitEntry, LiteralFingerprintIndex>;
  FingerprintIndex _index;
  Array<vvector<LitEntry>> _buckets;
  vstring _name;
};

class TermFingerprintIndex final : public TermIndexingStructure {
public:
  CLASS_NAME(TermFingerprintIndex);
  USE_ALLOCATOR(TermFingerprintIndex);
  void insert(TermList t, Literal *lit, Clause *cls) override;
  void remove(TermList t, Literal *lit, Clause *cls) override;

  TermFingerprintIndex(vstring name) : _name(name) {}

  TermQueryResultIterator getUnifications(
    TermList t,
    bool retrieveSubstitutions = true
  ) override;
  TermQueryResultIterator getUnificationsWithConstraints(
    TermList t,
    bool retrieveSubstitutions = true
  ) override { NOT_IMPLEMENTED; }
  TermQueryResultIterator getGeneralizations(
    TermList t,
    bool retrieveSubstitutions = true
  ) override;
  TermQueryResultIterator getInstances(
    TermList t,
    bool retrieveSubstitutions = true
  ) override;

  vstring name() { return _name; }

#if VDEBUG
  void markTagged() override {};
#endif
private:

  class TQRIterator {
  public:
    TQRIterator(TermEntryIterator results, TermList query);
    DECL_ELEMENT_TYPE(TermQueryResult);
    bool hasNext();
    OWN_ELEMENT_TYPE next();
    virtual bool prepareSubst() = 0;
  protected:
    TermEntryIterator _it;
    TermList _query;
    RobSubstitutionSP _subst;
    TermQueryResult _next;
    bool _hasNext;
  };

  TermQueryResultIterator getAll(TermList query);

  class UnificationIterator final : public TQRIterator {
  public:
    using TQRIterator::TQRIterator;
    bool prepareSubst() override;
  };

  class GeneralizationIterator final : public TQRIterator {
  public:
    using TQRIterator::TQRIterator;
    bool prepareSubst() override;
  };

  class InstanceIterator final : public TQRIterator {
  public:
    using TQRIterator::TQRIterator;
    bool prepareSubst() override;
  };

  friend class EntryIterator<TermEntry, TermFingerprintIndex>;
  FingerprintIndex _index;
  Array<vvector<TermEntry>> _buckets;
  vstring _name;
}; // class TermFingerprintIndex
} //namespace Indexing

#endif // __FingerprintIndex__
