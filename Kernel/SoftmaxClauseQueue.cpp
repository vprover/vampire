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
 * @file SoftmaxClauseQueue.cpp
 * Implements class SoftmaxClauseQueue of clause priority queues
 * @since 12/10/2022 Dagstuhl
 */

#include "Debug/Tracer.hpp"

#include "Lib/Allocator.hpp"
#include "Lib/Random.hpp"
#include "Lib/Environment.hpp"

#if VDEBUG
#include "Clause.hpp"
#endif

#include "SoftmaxClauseQueue.hpp"

#define MAX_HEIGHT 31

using namespace Lib;
using namespace Kernel;

SoftmaxClauseQueue::SoftmaxClauseQueue(DHMap<Clause*,std::pair<double,unsigned>>& scores)
    : _height(0), _total(0.0), _scores(scores)
{
  void* mem = ALLOC_KNOWN(sizeof(Node)+MAX_HEIGHT*sizeof(LinkInfo),"SoftmaxClauseQueue::Node");
  _left = reinterpret_cast<Node*>(mem);
#if VDEBUG
  _left->height = MAX_HEIGHT;
  _left->clause = nullptr;
#endif
  _left->nodes[0] = make_pair(nullptr,0.0);
}

/** Temporary!!! */
SoftmaxClauseQueue::~SoftmaxClauseQueue ()
{
  CALL("SoftmaxClauseQueue::~SoftmaxClauseQueue");

  removeAll();

  DEALLOC_KNOWN(_left,sizeof(Node)+MAX_HEIGHT*sizeof(LinkInfo),"ClauseQueue::Node");
} // SoftmaxClauseQueue::~SoftmaxClauseQueue

bool SoftmaxClauseQueue::lessThan(Clause* c1, ScoreInfo sc1, Clause* c2)
{
  CALL("SoftmaxClauseQueue::~lessThan");

  // based on ShuffleScoreQueue's lessThan - how to best prevent code reuse?
  auto sc2 = _scores.get(c2);
  // reversing the order here: NNs think large is good, queues think small is good
  if (sc1.first > sc2.first) {
    return true;
  }
  if (sc1.first < sc2.first) {
    return false;
  }

  // here, the second coord are just fixed random numbers for breaking ties (before we go down to number())
  if (sc1.second > sc2.second) {
    return true;
  }
  if (sc1.second < sc2.second) {
    return false;
  }

  return c1->number() < c2->number();
}

// left is a node with a value smaller than that of newNode and having a large enough height.
// this node is on the left of the inserted one
// lh is the height on which we search for the next node
/**
 * The following loop does all the necessary stuff for ClauseQueue (but maintining link lengths requries an addtional "post order" update)
 * 
  for (;;) {
    Node* next = left->nodes[lh];
    if (next == 0 || lessThan(c,next->clause)) {
      if (lh <= h) {
        left->nodes[lh] = newNode;
        newNode->nodes[lh] = next;
      }
      if (lh == 0) {
    	  return;
      }
      lh--;
      continue;
    }
    left = next;
  }
*/
double SoftmaxClauseQueue::integrate(Clause* c, ScoreInfo sc, Node* newNode, unsigned h, Node* left, unsigned lh)
{
  CALL("SoftmaxClauseQueue::integrate");

  double dist = 0.0;
  for (;;) {
    auto link = left->nodes[lh];
    Node* next = link.first;
    if (next == 0 || lessThan(c,sc,next->clause)) {
      if (lh == 0) {
        // don't need to change the lenght of a level-0 link
        left->nodes[0].first = newNode;
        newNode->nodes[0] = make_pair(next,sc.first);
        return dist + left->nodes[0].second;
      }
      double idist = integrate(c,sc,newNode,h,left,lh-1);
      if (lh <= h) {
        left->nodes[lh] = make_pair(newNode,idist);
        newNode->nodes[lh] = make_pair(next,link.second-idist);
        return dist + idist;
      }
      // the target stays the same, but we shoot further
      left->nodes[lh].second += sc.first;
      return 0.0; // We didn't care anymore, and higher up callers don't care either
    } else {
      left = next;
      dist += link.second;
    }
  }
}

void SoftmaxClauseQueue::insert(Clause* c)
{
  CALL("SoftmaxClauseQueue::insert");

  ScoreInfo sc = _scores.get(c);

  // select a random height between 0 and top
  unsigned h = 0;
  while (Random::getBit()) {
    h++;
  }
  if (h > _height) {
    if (_height < MAX_HEIGHT) {
      _height++;
    }
    h = _height;
    _left->nodes[h] = make_pair(nullptr,_total);
  }
  void* mem = ALLOC_KNOWN(sizeof(Node)+h*sizeof(LinkInfo),"SoftmaxClauseQueue::Node");
  Node* newNode = reinterpret_cast<Node*>(mem);
#if VDEBUG
  newNode->height = h;
#endif
  newNode->clause = c;
  // set newNode's nodes but, obviously, also update those who will now point to newNone
  // additionally, maintain the correct "volume" associated with each link
  integrate(c,sc,newNode,h,_left,_height);
  _total += sc.first; // adding the score of the to-be-inserted element to total
} // SoftmaxClauseQueue::insert

/**
 * Remove the clause c from the queue.
 * @since 30/12/2007 Manchester
 */
bool SoftmaxClauseQueue::remove(Clause* c)
{
  CALL("SoftmaxClauseQueue::remove");

  ScoreInfo sc = _scores.get(c);

  unsigned h = _height;
  Node* left = _left;

  for (;;) {
    Node* next = left->nodes[h].first;
    if (next && c == next->clause) {
      unsigned height = h;
      // found, first change the links going to next
      for (;;) {
	      left->nodes[h].first = next->nodes[h].first;
        left->nodes[h].second += next->nodes[h].second - sc.first;
	      if (h == 0) {
	        break;
	      }
	      h--;
        while (left->nodes[h].first != next) {
          left = left->nodes[h].first;
        }
      }
      // deallocate the node
      ASS_EQ(height,next->height);
      DEALLOC_KNOWN(next,sizeof(Node)+height*sizeof(LinkInfo),"SoftmaxClauseQueue::Node");
      while (_height > 0 && !_left->nodes[_height].first) {
	      _height--;
      }
      _total -= sc.first;
      return true;
    }

    if (next == 0 || lessThan(c,sc,next->clause)) {
      if(h==0) {
        // At the moment, it's evil to delete something that's not store,
        // because we preemptively decrease the length of traversed links just below
        ASSERTION_VIOLATION;
	      return false;
      }
      left->nodes[h].second -= sc.first;
      h--;
    }
    else {
      left = next;
    }
  }
} // SoftmaxClauseQueue::remove


/**
 * Randomly sample a clause proportionally to its score.
 * @since 17/10/2022 Prague
 */
Clause* SoftmaxClauseQueue::pop()
{
  CALL("SoftmaxClauseQueue::pop");
  ASS(_height >= 0);
  ASS(_left->nodes[0].first != nullptr);

  // double sample = Random::getDouble(0.0,_total)

  Node* node = _left->nodes[0].first;
  unsigned h = 0;
  _left->nodes[0].first = node->nodes[0].first;
  // on level 0, .second stays the same (and is equal 0.0, because _left does not store any clause)
  double cs = node->nodes[0].second;
  while (h < _height && _left->nodes[h+1].first == node) {
    h++;
    _left->nodes[h].first = node->nodes[h].first;
    _left->nodes[h].second += node->nodes[h].second - cs;
  }
  // now h is the height of the node
  Clause* c = node->clause;

  // deallocate the node
  ASS_EQ(h,node->height);
  DEALLOC_KNOWN(node,sizeof(Node)+h*sizeof(LinkInfo),"SoftmaxClauseQueue::Node");
  // update the length of the upper links
  while (++h <= _height) {
    _left->nodes[h].second -= cs;
  }
  while (_height > 0 && !_left->nodes[_height].first) {
    _height--;
  }

  return c;
} // SoftmaxClauseQueue::pop

/**
 * Remove all clauses from the queue.
 * @since 31/12/2007 Manchester
 */
void SoftmaxClauseQueue::removeAll()
{
  CALL("SoftmaxClauseQueue::removeAll");

  while (_left->nodes[0].first) {
    pop();
  }
} // removeAll

#if VDEBUG
void SoftmaxClauseQueue::output(ostream& str) const
{
  for (const Node* node = _left->nodes[0].first; node; node=node->nodes[0].first) {
    str << node->clause->toString() << '\n';
  }
} // SoftmaxClauseQueue::output
#endif
