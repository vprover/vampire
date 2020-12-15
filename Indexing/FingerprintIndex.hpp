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

  static const unsigned FINGERPRINT_SIZE = 2;
  static std::array<signed, FINGERPRINT_SIZE> fingerprint(TermList ts);
  FingerprintIndex();
  unsigned getBucket(TermList ts);
  void getUnifications(Stack<unsigned> &results, TermList ts);

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

  TermQueryResultIterator getUnifications(TermList t, bool retrieveSubstitutions = true) override;
  TermQueryResultIterator getUnificationsWithConstraints(TermList t, bool retrieveSubstitutions = true) override { NOT_IMPLEMENTED; }
  TermQueryResultIterator getGeneralizations(TermList t, bool retrieveSubstitutions = true) override { NOT_IMPLEMENTED; }
  TermQueryResultIterator getInstances(TermList t, bool retrieveSubstitutions = true) override { NOT_IMPLEMENTED; }

  bool generalizationExists(TermList t) override { NOT_IMPLEMENTED; }
#if VDEBUG
  void markTagged() override {};
#endif
private:
  struct Entry {
    Clause *cls;
    Literal *lit;
    TermList term;
    bool operator==(const Entry &other) const;
    bool operator!=(const Entry &other) const;
  };

  class ResultIterator {
  public:
    ResultIterator(const TermFingerprintIndex &index, Stack<unsigned> &&buckets);
    DECL_ELEMENT_TYPE(TermQueryResult);
    bool hasNext();
    void nextBucket();
    OWN_ELEMENT_TYPE next();
  private:
    const TermFingerprintIndex &_index;
    Stack<unsigned> _buckets;
    vvector<Entry>::const_iterator _entry;
    vvector<Entry>::const_iterator _end;
  };

  class UnificationIterator {
  public:
    UnificationIterator(ResultIterator results, TermList query);
    DECL_ELEMENT_TYPE(TermQueryResult);
    bool hasNext();
    OWN_ELEMENT_TYPE next();
  private:
    ResultIterator _it;
    TermList _query;
    RobSubstitutionSP _subst;
    TermQueryResult _next;
    bool _hasNext;
  };

  friend class ResultIterator;
  FingerprintIndex _index;
  Array<vvector<Entry>> _buckets;
}; // class TermFingerprintIndex
} //namespace Indexing

#endif // __FingerprintIndex__
