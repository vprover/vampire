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
#include "Clause.hpp"

#include "SoftmaxClauseQueue.hpp"

#define MAX_HEIGHT 31

using namespace Lib;
using namespace Kernel;

SoftmaxClauseQueue::SoftmaxClauseQueue(DHMap<Clause*,std::pair<float,unsigned>>& scores, bool talkative)
    : _talkative(talkative), _height(0), _total(0.0f), _scores(scores)
{
  void* mem = ALLOC_KNOWN(sizeof(Node)+MAX_HEIGHT*sizeof(LinkInfo),"SoftmaxClauseQueue::Node");
  _left = reinterpret_cast<Node*>(mem);
#if VDEBUG
  _left->id = 0;
  _left->height = MAX_HEIGHT;
  _left->clause = nullptr;
#endif
  _left->nodes[0] = make_pair(nullptr,0.0f);
}

/** Temporary!!! */
SoftmaxClauseQueue::~SoftmaxClauseQueue ()
{
  removeAll();

  DEALLOC_KNOWN(_left,sizeof(Node)+MAX_HEIGHT*sizeof(LinkInfo),"SoftmaxClauseQueue::Node");
} // SoftmaxClauseQueue::~SoftmaxClauseQueue

bool SoftmaxClauseQueue::lessThan(Clause* c1, ScoreInfo sc1, Clause* c2)
{
  // based on ShuffleScoreQueue's lessThan - how to best ensure code reuse?
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

void SoftmaxClauseQueue::insert(Clause* c)
{
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
    _left->nodes[h] = make_pair(nullptr,0.0f);
  }
  void* mem = ALLOC_KNOWN(sizeof(Node)+h*sizeof(LinkInfo),"SoftmaxClauseQueue::Node");
  Node* newNode = reinterpret_cast<Node*>(mem);
#if VDEBUG
  static unsigned ids = 0;
  newNode->id = ++ids;
  newNode->height = h;
#endif
  newNode->clause = c;

  // set newNode's nodes but, obviously, also update those that will now point to newNone
  // additionally, maintain the correct "volume" associated with each link
  Node* left = _left;
  unsigned lh = _height;
  // traversing the "overshooters" first
  while (lh > h) {
    auto& link = left->nodes[lh];
    Node* next = link.first;
    if (next == nullptr || lessThan(c,sc,next->clause)) {
      // the change is only in the distance traveled now
      // (and if next == nullptr, there are no guarantees about link.second anyway)
      link.second += sc.first;
      lh--;
    } else {
      // just move forward
      left = next;
    }
  }
  // these guys will shoot into newNode and we need to know, how far exactly this is going to be on each level
  // will use "update" for it
  LinkInfo update[MAX_HEIGHT];
  for (;;) {
    auto& link = left->nodes[lh];
    Node* next = link.first;
    if (next == nullptr || lessThan(c,sc,next->clause)) {
      // remember current "left" for level "lh" is "first" ...
      update[lh].first = left;
      if (lh == 0) {
        break;
      } else {
        lh--;
        // ... and start accumalating the distance in "second"
        // it's only important to zero this out from the first descend on,
        // (the node update[h] does not need to report the "distance traveled" upwards anymore)
        update[lh].second = 0.0f;
      }
    } else {
      left = next;
      update[lh].second += link.second;
    }
  }
  ASS_EQ(lh,0);
  ASS(left == update[0].first);
  // init "dist" by the last (not yer recorded) jump on level 0
  float dist = left->nodes[0].second;
  // go up again, and update nodes waiting for it
  for (;;) {
    Node* updNode = update[lh].first;
    newNode->nodes[lh].first = updNode->nodes[lh].first;
    updNode->nodes[lh].first = newNode;
    updNode->nodes[lh].second = dist;
    if (lh == h) {
      break;
    } else {
      // all the remaining jumps on level lh:
      dist += update[lh].second;
      // (notice we won't need to use update[h].second, so it's OK it contains rubbish)
      lh++;
    }
  }
  // what we need to finish off is newNode->nodes[lh].second
  // (which we didn't want to derive from updNode->nodes[lh].second using subtraction,
  //  so we keep hopping beyond newNode now)
  newNode->nodes[0].second = sc.first;
  dist = 0.0f;
  Node* right = newNode;
  unsigned rh = 0; // traveling at "rh", but aiming for "rh+1" to write the result to
  while (rh < h) {
    Node* target = newNode->nodes[rh+1].first;
    if (target == nullptr) {
      break;
    }
    while (right != target) {
      auto link = right->nodes[rh];
      right = link.first;
      dist += link.second;
    }
    rh++;
    newNode->nodes[rh].second = dist;
  }

  _total += sc.first; // adding the score of the to-be-inserted element to total

  // output(cout);
  ASS(consistent());
} // SoftmaxClauseQueue::insert

/**
 * Remove the clause c from the queue.
 * @since 30/12/2007 Manchester
 */
bool SoftmaxClauseQueue::remove(Clause* c)
{
  // cout << "Before remove of " << c->toString() << endl;
  // output(cout);

  ScoreInfo sc = _scores.get(c);

  unsigned h = _height;
  Node* left = _left;
  Node* found = nullptr;

  LinkInfo update[MAX_HEIGHT];
  update[h].second = 0.0f; // other second's get zero-ed out when we descend to meet them
  // as we go forward and down to locate the node (although, potentially, there is no such),
  // we remember the nodes that we will need to update with new dist
  // and keep collecting the traveled distances on each level (both in "update" like with "insert")
  for (;;) {
    auto link = left->nodes[h];
    Node* next = link.first;
    if (next && c == next->clause) {
      found = next;
      break;
    }
    if (next == nullptr || lessThan(c,sc,next->clause)) {
      if(h==0) {
        // with clause selection, we never delete things not previously stored
        // (However, we could. So feel free to remove the below assertion if you want.)
        ASSERTION_VIOLATION;
	      return false;
      }
      update[h].first = left;
      h--;
      update[h].second = 0.0f; // starting a new counter
    }
    else {
      left = next;
      update[h].second += link.second;
    }
  }

  unsigned height = h;
  // found! now change the links going to "found" and keep descending, still storing "left"'s in "update"
  for (;;) {
    left->nodes[h].first = found->nodes[h].first;
    if (h == 0) {
      break;
    }
    // (no need to strore "left" on level 0)
    update[h].first = left;
    h--;
    update[h].second = 0.0f; // starting a new counter
    while (left->nodes[h].first != found) {
      update[h].second += left->nodes[h].second;
      left = left->nodes[h].first;
    }
  }

  // deallocate the node
  ASS_EQ(height,found->height);
  DEALLOC_KNOWN(found,sizeof(Node)+height*sizeof(LinkInfo),"SoftmaxClauseQueue::Node");
  while (_height > 0 && !_left->nodes[_height].first) {
    _height--;
  }

  ASS_EQ(h,0);
  float dist = update[0].second; // does not include left->nodes[0].second
  Node* right = left;
  // we start from "left", which, on level 0, used to point to "found"
  // we start traversing from level 0
  while (h < _height) {
    Node* target = update[h+1].first->nodes[h+1].first;
    if (target == nullptr) {
      // let's add overshooters' distance (later on, we only descend from "h" again down to 0)
      for (unsigned th = h+1; th <= _height; th++) {
        dist += update[th].second;
      }
      break;
    }
    while (right != target) {
      auto link = right->nodes[h];
      right = link.first;
      dist += link.second;
    }
    h++;
    update[h].first->nodes[h].second = dist;
    dist += update[h].second;
  }
  // nobody is overshooting "right" anymore, but we need to find the end to properly compute the new "_total"
  for (;;) {
    while (right->nodes[h].first) {
      dist += right->nodes[h].second;
      right = right->nodes[h].first;
    }
    if (h==0) {
      break;
    }
    h--;
  }
  ASS_EQ(h,0);
  ASS(right->nodes[0].first == nullptr);
  _total = dist + right->nodes[0].second;

  // cout << "After remove" << endl;
  // output(cout);
  ASS(consistent());
  return true;
} // SoftmaxClauseQueue::remove

/**
 * Randomly sample a clause proportionally to its score.
 * @since 19/10/2022 Prague
 */
Clause* SoftmaxClauseQueue::pop()
{
  ASS(_height >= 0);
  ASS(_left->nodes[0].first != nullptr);

  float sample = Random::getFloat(0.0f,_total);
  unsigned h = _height;
  Node* node = _left;

  if (_total == std::numeric_limits<float>::infinity()) {
    node = _left->nodes[0].first;
    if (_talkative) {
      cout << "p: nan" << endl; // we say "nan", because maybe we are storing more than one infinity clause, but we are picking the first
    }
    goto clause_found;
  }

  for (;;) {
    LinkInfo li = node->nodes[h];
    Node* next = li.first;
    float mass = li.second;
    if (next == nullptr || sample - mass < 0.0f ||    // the link on level h shoots out, or is long enough to satisfy sample, or
       (node != _left && sample - mass == sample)) { // or subtraction stopped working (underflows? / zero mass elelements?)
      if (h > 0) {
        h--;
        continue;
      }
      ASS(next != nullptr || sample - mass < 0.0f); // wanting to overshoot a nullptr for h == 0 is evil. It means we jumped out of our collection
      // found our node!
      // cout << "popping an element of mass " << mass << endl;
      if (_talkative) {
        cout << "p: " << mass/_total << endl;
      }
      break;
    } else {
      sample = sample - mass;
      node = node->nodes[h].first;
    }
  }
  ASS_EQ(h,0);
  ASS(node != nullptr);

  clause_found:
  Clause* cl = node->clause;
  // could we do better here by having kept some update info during the decent?
  // (However, note that unlike with remove, we don't know the score of
  //  the to-be-removed element for shorting the tall links at the moment of the descent)
  remove(cl);

  ASS(consistent());
  return cl;
} // SoftmaxClauseQueue::pop

/**
 * Abusing the old ClauseQueue pop,
 * the extra "Softmax" invariants are not maintained.
 * @since 17/10/2022 Prague
 */
void SoftmaxClauseQueue::dropFirst()
{
  ASS(_height >= 0);
  ASS(_left->nodes[0].first != nullptr);

  Node* node = _left->nodes[0].first;
  unsigned h = 0;
  _left->nodes[0].first = node->nodes[0].first;
  while (h < _height && _left->nodes[h+1].first == node) {
    h++;
    _left->nodes[h].first = node->nodes[h].first;
  }

  // deallocate the node
  DEALLOC_KNOWN(node,sizeof(Node)+h*sizeof(LinkInfo),"SoftmaxClauseQueue::Node");
  while (_height > 0 && ! _left->nodes[_height].first) {
    _height--;
  }
} // SoftmaxClauseQueue::dropFirst

/**
 * Remove all clauses from the queue.
 * @since 31/12/2007 Manchester
 */
void SoftmaxClauseQueue::removeAll()
{
  while (_left->nodes[0].first) {
    dropFirst();
  }

  _total = 0.0f;
} // removeAll

#if VDEBUG
/**
 * Are the two given POSITIVE doubles roughly the same?
 */
static bool roughlyTheSame(float a, float b) {
  ASS_G(a,0.0f);
  ASS_G(b,0.0f);
  return abs((a-b)/max(a,b)) < 0.0000001f;
}

bool SoftmaxClauseQueue::consistentRec(Node* cur, Node* whatsSeen, float& sumLinks) const
{
  if (cur == nullptr) {
    for (unsigned h = 0; h <= _height; h++) {
      whatsSeen->nodes[h] = make_pair(nullptr,0.0f);
    }
    return true;
  }
  if (!consistentRec(cur->nodes[0].first,whatsSeen,sumLinks)) {
    // fail fast
    return false;
  }
  // keep checking, everything was OK until now
  ScoreInfo sc = (cur == _left) ? std::make_pair(0.0f,0u) : _scores.get(cur->clause);
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
    if ((link.first != nullptr || h == 0) && // h > 0 nullptrs are fine with rubbish score mass
        cur != _left && !roughlyTheSame(link.second,whatsSeen->nodes[h].second + sc.first)) {
      cout << "Node " << cur->id << " failed the mass check for h = " << h << endl;
      cout << "link.second is " << link.second << " and whatsSeen->nodes[h].second + sc.first is " << whatsSeen->nodes[h].second + sc.first << endl;
      return false;
    }
    whatsSeen->nodes[h].second = 0.0f; // from close by
  }

  return true;
}

bool SoftmaxClauseQueue::consistent() const
{
  void* mem = ALLOC_KNOWN(sizeof(Node)+_height*sizeof(LinkInfo),"SoftmaxClauseQueue::Node");
  Node* whatsSeen = reinterpret_cast<Node*>(mem);
  float sumLinks = 0.0f;
  bool res = consistentRec(_left,whatsSeen,sumLinks);
  DEALLOC_KNOWN(whatsSeen,sizeof(Node)+_height*sizeof(LinkInfo),"SoftmaxClauseQueue::Node");
  // cout << "Total sum check diff " << sumLinks - _total << " from " <<  sumLinks << " and " << _total << endl;
  if (_left->nodes[0].first && // non-empty
      !roughlyTheSame(sumLinks,_total)) {
    cout << "Total sum check failed." << endl;
    cout << "sumLinks is " << sumLinks << " and _total is " << _total << endl;
    cout << "The difference being " << sumLinks-_total << endl;
    return false;
  }
  return res;
}

void SoftmaxClauseQueue::output(ostream& str) const
{
  str << "SoftmaxClauseQueue with a total " << _total << endl;
  for (const Node* node = _left; node; node=node->nodes[0].first) {
    Clause* cl = node->clause;
    unsigned height;
    if (cl) {
      height = node->height;
      str << "Node " << node->id << " of mass " << _scores.get(node->clause).first << " and with clause " << node->clause->toString() << endl;
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