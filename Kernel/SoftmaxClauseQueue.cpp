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
  _left->id = 0;
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

  DEALLOC_KNOWN(_left,sizeof(Node)+MAX_HEIGHT*sizeof(LinkInfo),"SoftmaxClauseQueue::Node");
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
    if (next == nullptr || lessThan(c,sc,next->clause)) {
      if (lh == 0) {
        // don't need to change the score mass of a level-0 link
        left->nodes[0].first = newNode;
        newNode->nodes[0] = make_pair(next,sc.first);
        return dist + left->nodes[0].second;
      }
      double idist = integrate(c,sc,newNode,h,left,lh-1);
      if (lh <= h) {
        left->nodes[lh] = make_pair(newNode,idist);
        newNode->nodes[lh] = make_pair(next,link.second-idist+sc.first); // not much sense here, if next == nullptr
        return dist + idist;
      }
      // the target stays the same, but we shoot further
      // (unless left->nodes[lh].first == nullptr, and again, then the update below makes no sense)
      left->nodes[lh].second += sc.first;
      return 0.0; // We didn't care anymore, and higher-up callers don't care either
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

  // zero score elements are evil for sampling
  ASS_G(sc.first,0);

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
    _left->nodes[h] = make_pair(nullptr,0.0);
  }
  void* mem = ALLOC_KNOWN(sizeof(Node)+h*sizeof(LinkInfo),"SoftmaxClauseQueue::Node");
  Node* newNode = reinterpret_cast<Node*>(mem);
#if VDEBUG
  static unsigned ids = 0;
  newNode->id = ++ids;
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
        // as usual, the below is bogus if the pointee is nullptr
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
        // At the moment, it's evil to delete something that's not stored,
        // because we preemptively decrease the length of traversed links just below
        // (the next == 0 case would be fine, but the other wouldn't)
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
 * @since 19/10/2022 Prague
 */
Clause* SoftmaxClauseQueue::pop()
{
  CALL("SoftmaxClauseQueue::pop");
  ASS(_height >= 0);
  ASS(_left->nodes[0].first != nullptr);

  double sample = Random::getDouble(0.0,_total);
  // cout << "Sample " << sample <<" out of total " << _total << endl;

  unsigned h = _height;
  Node* node = _left;

  for (;;) {
    LinkInfo li = node->nodes[h];
    Node* next = li.first;
    double mass = li.second;
    if (next == nullptr || sample - mass < 0.0 ||    // the link on level h shoots out, or is long enough to satisfy sample, or
       (node != _left && sample - mass == sample)) { // or subtraction stopped working (underflows? / zero mass elelements?)
      if (h > 0) {
        h--;
        continue;
      }
      ASS(next != nullptr || sample - mass < 0.0); // wanting to overshoot a nullptr for h == 0 is evil. It means we jumped out of our collection
      // found our node!
      // cout << "popping an element of mass " << mass << endl;
      break;
    } else {
      sample = sample - mass;
      node = node->nodes[h].first;
    }
  }
  ASS_EQ(h,0);
  ASS(node != nullptr);

  Clause* cl = node->clause;
  // could we do better here by having kept some update info during the decent?
  // (However, note that unlike with remove, we don't know the score of the to be removed
  //  element for shorting the tall links at the moment of the descent)
  remove(cl);
  return cl;
} // SoftmaxClauseQueue::pop

/**
 * Adapting the old ClauseQueue pop to maintain score mass invariants too.
 * @since 17/10/2022 Prague
 */
Clause* SoftmaxClauseQueue::popOld()
{
  CALL("SoftmaxClauseQueue::popOld");
  ASS(_height >= 0);
  ASS(_left->nodes[0].first != nullptr);

  Node* node = _left->nodes[0].first;
  unsigned h = 0;
  _left->nodes[0].first = node->nodes[0].first;
  // on level 0, .second stays the same (and is equal 0.0, because _left does not store any clause)
  double cs = node->nodes[0].second;
  _total -= cs;
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
} // SoftmaxClauseQueue::popOld

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
bool SoftmaxClauseQueue::consistentRec(Node* cur, Node* whatsSeen, double& sumLinks) const
{
  CALL("SoftmaxClauseQueue::consistentRec");

  if (cur == nullptr) {
    for (unsigned h = 0; h <= _height; h++) {
      whatsSeen->nodes[h] = make_pair(nullptr,0.0);
    }
    return true;
  }
  if (!consistentRec(cur->nodes[0].first,whatsSeen,sumLinks)) {
    // fail fast
    return false;
  }
  // keep checking, everything was OK until now
  ScoreInfo sc = (cur == _left) ? std::make_pair(0.0,0u) : _scores.get(cur->clause);
  sumLinks += sc.first;
  for (unsigned h = 0; h <= _height; h++) {
    if (h > cur->height) {
      // "the beam runs above our head"
      whatsSeen->nodes[h].second += sc.first;
      continue;
    }
    auto link = cur->nodes[h];
    // the pointers are fine:
    if (link.first != whatsSeen->nodes[h].first) {
      cout << "Node " << cur->id << " failed the link check for h = " << h << endl;
      return false;
    }
    whatsSeen->nodes[h].first = cur;  // now you see me
    // the score mass is fine:
    if ((link.first != nullptr || h == 0) && // h > 0 nullptrs are fine with rubbish score mass (we wont want to just to the nullptr place)
        link.second != whatsSeen->nodes[h].second + sc.first) {
      cout << "Node " << cur->id << " failed the mass check for h = " << h << endl;
      return false;
    }
    whatsSeen->nodes[h].second = 0.0; // from close by
  }

  return true;
}

bool SoftmaxClauseQueue::consistent() const
{
  CALL("SoftmaxClauseQueue::consistent");

  void* mem = ALLOC_KNOWN(sizeof(Node)+_height*sizeof(LinkInfo),"SoftmaxClauseQueue::Node");
  Node* whatsSeen = reinterpret_cast<Node*>(mem);
  double sumLinks = 0.0;
  bool res = consistentRec(_left,whatsSeen,sumLinks);
  DEALLOC_KNOWN(whatsSeen,sizeof(Node)+_height*sizeof(LinkInfo),"SoftmaxClauseQueue::Node");
  if (sumLinks != _total) {
    cout << "Total sum check failed." << endl;
    return false;
  }
  return res;
}

void SoftmaxClauseQueue::output(ostream& str) const
{
  CALL("SoftmaxClauseQueue::output");

  ASS(consistent());

  str << "SoftmaxClauseQueue with a total " << _total << endl;
  for (const Node* node = _left; node; node=node->nodes[0].first) {
    Clause* cl = node->clause;
    unsigned height;
    if (cl) {
      height = node->height;
      str << "Node " << node->id << " of mass " << node->clause->weight() << " and with clause " << node->clause->toString() << endl;
    } else {
      height = _height;
      str << "Node " << node->id << " with no clause" << endl;
    }
    for (unsigned h = 0; h <= height; h++) {
      str << "(";
      if (node->nodes[h].first) {
        str << std::setw(3) << node->nodes[h].first->id;
      } else {
        str << "nil";
      }
      str << "," << std::setw(3) << node->nodes[h].second << ") | ";
    }
    str << endl;
  }
  str << endl;
} // SoftmaxClauseQueue::output
#endif
