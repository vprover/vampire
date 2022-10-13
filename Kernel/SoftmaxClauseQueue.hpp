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
 * @file SoftmaxClauseQueue.hpp
 * Defines class SoftmaxClauseQueue.
 *
 * @since 12/10/2022 Dagstuhl
 */

#ifndef __SoftmaxClauseQueue__
#define __SoftmaxClauseQueue__

#if VDEBUG
#include <ostream>
using namespace std;
#endif

#include "Debug/Assertion.hpp"

#include "Lib/Reflection.hpp"

namespace Kernel {

class Clause;

/**
 * Based on ClauseQueue, this class assumes Clauses have probability scores (logits)
 * and is designed to efficiently sample the softmax (with a fixed temperatore) distribution
 * corresponding to these logits (see https://en.wikipedia.org/wiki/Softmax_function)
 *
 * On the skip list side, we need to extend the nodes with partial sums, to know how
 * much probability volume we skip over what traversing each "highway".
 *
 * @since 30/12/2007 Manchester
 * @since 12/10/2022 Dagstuhl
 */
class SoftmaxClauseQueue
{
public:
  SoftmaxClauseQueue();
  virtual ~SoftmaxClauseQueue();
  void insert(Clause*);
  bool remove(Clause*);
  void removeAll();
  Clause* pop();
  /** True if the queue is empty */
  bool isEmpty() const
  { return _left->nodes[0] == 0; }
#if VDEBUG
  void output(ostream&) const;
#endif

  friend class Iterator;
protected:
  /** comparison of clauses */
  virtual bool lessThan(Clause*,Clause*) = 0;
  /** Nodes in the skip list */
  class Node {
  public:
    /** Clause at this node */
    Clause* clause;
    /** Links to other nodes on the right, can be of any length */
    Node* nodes[1];
  };
  /** Height of the leftmost node minus 1 */
  unsigned _height;
  /** the leftmost node with the dummy key and value */
  Node* _left;

public:
  /** Iterator over the queue
   * @since 04/01/2008 flight Manchester-Murcia
   */
  class Iterator {
  public:
    DECL_ELEMENT_TYPE(Clause*);

    /** Create a new iterator */
    inline explicit Iterator(SoftmaxClauseQueue& queue)
      : _current(queue._left)
    {}
    /** true if there is a next clause */
    inline bool hasNext() const
    { return _current->nodes[0]; }
    /** return the next clause */
    inline Clause* next()
    {
      _current = _current->nodes[0];
      ASS(_current);
      return _current->clause;
    }
  private:
    /** Current node */
    Node* _current;
  }; // class SoftmaxClauseQueue::Iterator
}; // class SoftmaxClauseQueue

} // namespace Kernel

#endif
