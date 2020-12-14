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
#include "Lib/Set.hpp"
#include "Lib/Stack.hpp"

namespace Indexing {
class FingerprintIndex {
public:
  CLASS_NAME(FingerprintIndex);
  USE_ALLOCATOR(FingerprintIndex);

  static const unsigned FINGERPRINT_SIZE = 2;
  static std::array<signed, FINGERPRINT_SIZE> fingerprint(TermList ts);
  FingerprintIndex();
  ~FingerprintIndex();
  unsigned makeBucket(TermList ts);
  void getUnifications(Stack<unsigned> &results, TermList ts);

private:
  class Node {
  public:
    virtual ~Node() = default;
    virtual unsigned makeBucket(const std::array<signed, FingerprintIndex::FINGERPRINT_SIZE> &fingerprint, unsigned &fresh, unsigned index) = 0;
    virtual void getUnifications(Stack<unsigned> &results, const std::array<signed, FingerprintIndex::FINGERPRINT_SIZE> &fingerprint, unsigned index) = 0;
  };

  class Leaf final : public Node {
  public:
    CLASS_NAME(FingerprintIndex::Leaf);
    USE_ALLOCATOR(FingerprintIndex::Leaf);
    Leaf(unsigned);
    unsigned makeBucket(const std::array<signed, FingerprintIndex::FINGERPRINT_SIZE> &fingerprint, unsigned &fresh, unsigned index);
    void getUnifications(Stack<unsigned> &results, const std::array<signed, FingerprintIndex::FINGERPRINT_SIZE> &fingerprint, unsigned index);
  private:
    unsigned _bucket;
  };

  class Branch final : public Node {
  public:
    CLASS_NAME(FingerprintIndex::Branch);
    USE_ALLOCATOR(FingerprintIndex::Branch);
    ~Branch();
    unsigned makeBucket(const std::array<signed, FingerprintIndex::FINGERPRINT_SIZE> &fingerprint, unsigned &fresh, unsigned index);
    void getUnifications(Stack<unsigned> &results, const std::array<signed, FingerprintIndex::FINGERPRINT_SIZE> &fingerprint, unsigned index);
  private:
    Map<signed, Node *> _children;
  };

  Node *_root;
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
    ResultIterator(TermFingerprintIndex *index, Stack<unsigned> &&buckets);
    DECL_ELEMENT_TYPE(TermQueryResult);
    bool hasNext();
    OWN_ELEMENT_TYPE next();
  private:
    TermFingerprintIndex *_index;
    Stack<unsigned> _buckets;
    Set<Entry>::Iterator _entryIt;
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
  Array<Set<Entry>> _buckets;
}; // class TermFingerprintIndex
} //namespace Indexing

#endif // __FingerprintIndex__
