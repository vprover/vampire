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
#include "Lib/DHMap.hpp"
#include "Kernel/ClauseQueue.hpp"

namespace Kernel {

class Clause;

/**
 * Based on ClauseQueue, this class assumes Clauses have probability scores (logits)
 * and is designed to efficiently sample the softmax (with a fixed temperature) distribution
 * corresponding to these logits (see https://en.wikipedia.org/wiki/Softmax_function)
 *
 * On the skip list side, we need to extend the nodes with partial sums, to know how
 * much probability volume we skip over when traversing each "highway".
 *
 * @since 30/12/2007 Manchester
 * @since 12/10/2022 Dagstuhl
 */
class SoftmaxClauseQueue :
  public AbstractClauseQueue
{
protected:
  class Node;
public:
  SoftmaxClauseQueue(DHMap<Clause*,std::pair<float,unsigned>>& scores, bool talkative);
  virtual ~SoftmaxClauseQueue() override;
  void insert(Clause*) override;
  bool remove(Clause*) override;
  void removeAll();
  Clause* pop() override;
  /** True if the queue is empty */
  bool isEmpty() const override
  { return _left->nodes[0].first == 0; }
#if VDEBUG
  bool consistent() const;
  bool consistentRec(Node*, Node*, float&) const;
  void output(ostream&) const override;
#endif

  friend class Iterator;
protected:
  // just a helper to implement removeAll
  void dropFirst();

  // the pair means: (the node pointed to, the score mass traversed by jumping)
  // if .first == nullptr, .second is undef unless on h == 0 (in which case it's the score mass of the stored clause)
  typedef std::pair<Node*,float> LinkInfo;

  /** Nodes in the skip list */
  class Node {
  public:
#if VDEBUG
    unsigned id;
    unsigned height;
#endif
    /** Clause at this node */
    Clause* clause;
    /** Links to other nodes on the right, can be of any length;
     *  associated with each pointer is the score-distance traversed by the corresponding jump
    */
    LinkInfo nodes[1];
  };
  /** Report the probability of having selected that particular clause just now (during pop)*/
  bool _talkative;
  /** Height of the leftmost node minus 1 */
  unsigned _height;
  /** the leftmost node with the dummy key and value */
  Node* _left;
  /** Sum of scores of all the inserted elements. */
  float _total;

  typedef std::pair<float,unsigned> ScoreInfo; // the pair means: (the actual score, distinguishing random salt)
  const DHMap<Clause*,ScoreInfo>& _scores;

  bool lessThan(Clause* c1, ScoreInfo sc1, Clause* c2);
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
    { return _current->nodes[0].first; }
    /** return the next clause */
    inline Clause* next()
    {
      _current = _current->nodes[0].first;
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
