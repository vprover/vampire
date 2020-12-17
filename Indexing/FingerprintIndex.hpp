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

namespace Indexing {
class FingerprintIndex {
public:
  CLASS_NAME(FingerprintIndex);
  USE_ALLOCATOR(FingerprintIndex);

  static const unsigned FINGERPRINT_SIZE = 6;
  static std::array<signed, FINGERPRINT_SIZE> fingerprint(TermList ts);
  FingerprintIndex();
  unsigned getBucket(TermList ts);
  void getUnifications(Stack<unsigned> &results, TermList ts);
  void getGeneralizations(Stack<unsigned> &results, TermList ts);
  void getInstances(Stack<unsigned> &results, TermList ts);

private:
  vmap<std::pair<unsigned, signed>, unsigned> _edges;
  unsigned _fresh_node;
  unsigned _fresh_bucket;
}; // class FingerprintIndex

class TermFingerprintIndex final : public TermIndexingStructure {
public:
  CLASS_NAME(TermFingerprintIndex);
  USE_ALLOCATOR(TermFingerprintIndex);
  void insert(TermList t, Literal *lit, Clause *cls) override;
  void remove(TermList t, Literal *lit, Clause *cls) override;

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
  );

#if VDEBUG
  void markTagged() override {};
#endif
private:
  struct Entry {
    Clause *cls;
    Literal *lit;
    TermList term;
    bool operator==(const Entry &other) const;
  };

  class EntryIterator {
  public:
    EntryIterator(
      const TermFingerprintIndex &index,
      Stack<unsigned> &&buckets
    );
    DECL_ELEMENT_TYPE(Entry);
    bool hasNext();
    void nextBucket();
    OWN_ELEMENT_TYPE next();
  private:
    const TermFingerprintIndex &_index;
    Stack<unsigned> _buckets;
    vvector<Entry>::const_iterator _entry;
    vvector<Entry>::const_iterator _end;
  };

  class TQRIterator {
  public:
    TQRIterator(EntryIterator results, TermList query);
    DECL_ELEMENT_TYPE(TermQueryResult);
    bool hasNext();
    OWN_ELEMENT_TYPE next();
    virtual bool prepareSubst() = 0;
  protected:
    EntryIterator _it;
    TermList _query;
    RobSubstitutionSP _subst;
    TermQueryResult _next;
    bool _hasNext;
  };

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

  friend class EntryIterator;
  FingerprintIndex _index;
  Array<vvector<Entry>> _buckets;
}; // class TermFingerprintIndex
} //namespace Indexing

#endif // __FingerprintIndex__
