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
 * @file ClauseQueue.hpp
 * Defines class ClauseQueue.
 *
 * @since 30/12/2007 Manchester
 */

#ifndef __ClauseQueue__
#define __ClauseQueue__

#include <ostream>

#include "Debug/Assertion.hpp"

#include "Lib/Reflection.hpp"

#include "absl/container/btree_set.h"

namespace Kernel {

class Clause;

/**
 * A clause priority queue backed by absl::btree_set for cache-locality.
 * The comparison of elements is made using the virtual function lessThan.
 * @since 30/12/2007 Manchester
 */
class ClauseQueue
{
public:
  ClauseQueue();
  virtual ~ClauseQueue();
  void insert(Clause*);
  bool remove(Clause*);
  void removeAll();
  Clause* pop();
  /** True if the queue is empty */
  bool isEmpty() const
  { return _set.empty(); }
  void output(std::ostream&) const;

  friend class Iterator;
protected:
  /** comparison of clauses */
  virtual bool lessThan(Clause*,Clause*) = 0;

private:
  struct Comparator {
    ClauseQueue* queue;
    bool operator()(Clause* a, Clause* b) const {
      return queue->lessThan(a, b);
    }
  };

  using SetType = absl::btree_set<Clause*, Comparator>;
  SetType _set;

public:
  /** Iterator over the queue
   * @since 04/01/2008 flight Manchester-Murcia
   */
  class Iterator {
  public:
    DECL_ELEMENT_TYPE(Clause*);

    /** Create a new iterator */
    inline explicit Iterator(ClauseQueue& queue)
      : _it(queue._set.begin()), _end(queue._set.end())
    {}
    /** true if there is a next clause */
    inline bool hasNext() const
    { return _it != _end; }
    /** return the next clause */
    inline Clause* next()
    {
      ASS(_it != _end);
      return *_it++;
    }
  private:
    /** Current position */
    SetType::const_iterator _it;
    /** End position */
    SetType::const_iterator _end;
  }; // class ClauseQueue::Iterator

}; // class ClauseQueue

} // namespace Kernel

#endif
