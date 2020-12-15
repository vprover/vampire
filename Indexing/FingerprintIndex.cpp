/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#include "Kernel/RobSubstitution.hpp"
#include "Lib/Metaiterators.hpp"
#include "TermIndexingStructure.hpp"
#include "FingerprintIndex.hpp"
#include <iostream>

static const signed A = -1, B = -2, N = -3;

namespace Indexing {
std::array<signed, FingerprintIndex::FINGERPRINT_SIZE> FingerprintIndex::fingerprint(TermList p)
{
  CALL("FingerprintIndex::fingerprint");
  std::array<signed, FINGERPRINT_SIZE> result{N};
  ASS(!p.isVar());

  Term *t = p.term();
  result[0] = t->functor();
  if (t->arity() == 0) {
    return result;
  }

  TermList *p1 = t->nthArgument(0);
  if (p1->isVar()) {
    result[1] = A;
    result[4] = B;
    result[5] = B;
  }
  else {
    Term *t1 = p1->term();
    result[1] = t1->functor();
    if(t1->arity() > 0) {
      TermList *p11 = t1->nthArgument(0);
      result[4] = p11->isVar() ? A : p11->term()->functor();
    }
    if(t1->arity() > 1) {
      TermList *p12 = t1->nthArgument(1);
      result[5] = p12->isVar() ? A : p12->term()->functor();
    }
  }

  if(t->arity() == 1) {
    return result;
  }
  TermList *p2 = t->nthArgument(1);
  result[2] = p2->isVar() ? A : p2->term()->functor();

  if(t->arity() == 2) {
    return result;
  }
  TermList *p3 = t->nthArgument(2);
  result[3] = p3->isVar() ? A : p3->term()->functor();

  return result;
}

FingerprintIndex::FingerprintIndex() : _fresh_node(0), _fresh_bucket(0) {}

unsigned FingerprintIndex::getBucket(TermList t)
{
  CALL("FingerprintIndex::getBucket");
  auto fp = fingerprint(t);
  unsigned node = 0;
  for(unsigned i = 0; i < FINGERPRINT_SIZE; i++) {
    unsigned &next = _edges[std::make_pair(node, fp[i])];
    if(!next) {
      next = i + 1 == FINGERPRINT_SIZE ? _fresh_bucket++ : ++_fresh_node;
    }
    node = next;
  }
  return node;
}

static void unifications(
  Stack<unsigned> &results,
  const vmap<std::pair<unsigned, signed>, unsigned> &edges,
  const std::array<signed, FingerprintIndex::FINGERPRINT_SIZE> &fp,
  unsigned node,
  unsigned index
) {
  CALL("FingerprintIndex::getUnifications::unifications");
  if(index == FingerprintIndex::FINGERPRINT_SIZE) {
    results.push(node);
    return;
  }
  signed fpi = fp[index];
  auto do_edge = [&](signed edge) {
    auto search = edges.find(std::make_pair(node, edge));
    if(search != edges.end()) {
      unifications(results, edges, fp, search->second, index + 1);
    }
  };
  auto edges_if = [&](bool (*condition)(signed)) {
    auto lower = std::make_pair(node, std::numeric_limits<signed>::lowest());
    auto upper = std::make_pair(node, std::numeric_limits<signed>::max());
    auto lower_bound = edges.lower_bound(lower);
    auto upper_bound = edges.upper_bound(upper);
    for(auto it = lower_bound; it != upper_bound; it++) {
      signed edge = it->first.second;
      if(condition(edge)) {
        unifications(results, edges, fp, it->second, index + 1);
      }
    }
  };

  switch (fpi) {
    case N:
      do_edge(B);
      do_edge(N);
      break;
    case B:
      edges_if([](signed edge) { return true; });
      break;
    case A:
      edges_if([](signed edge) { return edge != N; });
      break;
    default:
      ASS_GE(fpi, 0);
      do_edge(fpi);
      do_edge(A);
      do_edge(B);
      break;
  }
}

void FingerprintIndex::getUnifications(Stack<unsigned> &results, TermList t) {
  CALL("FingerprintIndex::getUnifications");
  auto fp = fingerprint(t);
  unifications(results, _edges, fp, 0, 0);
}

bool TermFingerprintIndex::Entry::operator==(const Entry &other) const {
  return cls == other.cls && lit == other.lit && term == other.term;
}

bool TermFingerprintIndex::Entry::operator!=(const Entry &other) const {
  return cls != other.cls || lit != other.lit || term != other.term;
}

TermFingerprintIndex::ResultIterator::ResultIterator(
  const TermFingerprintIndex &index,
  Stack<unsigned> &&buckets
) :
  _index(index),
  _buckets(buckets)
{
  nextBucket();
}

void TermFingerprintIndex::ResultIterator::nextBucket() {
  if(!_buckets.isEmpty()) {
    unsigned bucket = _buckets.pop();
    auto &entries = _index._buckets[bucket];
    _entry = entries.begin();
    _end = entries.end();
  }
}

bool TermFingerprintIndex::ResultIterator::hasNext() {
  CALL("TermFingerprintIndex::ResultIterator::hasNext");
  while(_entry == _end) {
    if(_buckets.isEmpty()) {
      return false;
    }
    nextBucket();
  }
  return true;
}

TermQueryResult TermFingerprintIndex::ResultIterator::next() {
  CALL("TermFingerprintIndex::ResultIterator::next");
  Entry entry = *_entry++;
  return TermQueryResult(entry.term, entry.lit, entry.cls);
}

TermFingerprintIndex::UnificationIterator::UnificationIterator(
  ResultIterator it,
  TermList query
) :
  _it(it),
  _query(query),
  _subst(new RobSubstitution()),
  _next(),
  _hasNext(false)
{}

bool TermFingerprintIndex::UnificationIterator::hasNext() {
  CALL("TermFingerprintIndex::UnificationIterator::hasNext");
  if(_hasNext) {
    return true;
  }
  //std::cout << "candidates for " << _query << std::endl;
  while(_it.hasNext()) {
    _next = _it.next();
    //std::cout << _next.term << std::endl;
    _subst->reset();
    if(_subst->unify(_query, 0, _next.term, 1)) {
      _next.substitution =
        ResultSubstitution::fromSubstitution(_subst.ptr(), 0, 1);
      _hasNext = true;
      return true;
    }
  }
  //std::cout << "done" << std::endl;
  return false;
}

TermQueryResult TermFingerprintIndex::UnificationIterator::next() {
  CALL("TermFingerprintIndex::UnificationIterator::next");
  //std::cout << _query << " unifies with " << _next.term << std::endl;
  //std::cout << _subst->toString() << std::endl;
  _hasNext = false;
  return _next;
}

void TermFingerprintIndex::insert(TermList trm, Literal *lit, Clause *cls)
{
  CALL("TermFingerprintIndex::insert");
  //std::cout << "insert: " << trm << " in " << *lit << std::endl;
  _buckets[_index.getBucket(trm)].emplace_back(Entry{cls, lit, trm});
}

void TermFingerprintIndex::remove(TermList trm, Literal *lit, Clause *cls)
{
  CALL("TermFingerprintIndex::remove");
  //std::cout << "remove: " << trm << " in " << *lit << std::endl;
  auto &entries = _buckets[_index.getBucket(trm)];
  Entry remove {cls, lit, trm};
  for(auto it = entries.begin(); it != entries.end(); ++it) {
    if(*it == remove) {
      entries.erase(it);
      break;
    }
  }
}

TermQueryResultIterator TermFingerprintIndex::getUnifications(TermList t, bool retrieveSubstitutions)
{
  CALL("TermFingerprintIndex::getUnifications");
  Stack<unsigned> buckets;
  _index.getUnifications(buckets, t);
  return
    pvi(UnificationIterator(ResultIterator(*this, std::move(buckets)), t));
}
} // namespace Indexing
