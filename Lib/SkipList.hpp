/**
 * @file SkipList.hpp
* Implements skip lists storing a key and a value.
 *
 * @since 03/05/2006 Bellevue
 */


#ifndef __SkipList__
#  define __SkipList__

#include "../Debug/Tracer.hpp"

#include "Comparison.hpp"
#include "Random.hpp"

#define SKIP_LIST_MAX_HEIGHT 32

namespace Lib
{

/**
 * Skip lists storing a value of class Value.
 * The class ValueComparator should contain a function compare used to
 * compare Values.
 * @since 04/05/2006 Bellevue
 */
template <class Value,class ValueComparator>
class SkipList
{
public:
  class Node {
  public:
    Value value;
    Node* nodes[1];
  };
  /**
   * Insert an element in the skip list.
   * @since 04/05/2006 Bellevue
   */
  void insert(Value val)
  {
    CALL("SkipList::insert");

    // select a random height between 0 and top
    unsigned h = 0;
    while (Random::getBit()) {
      h++;
    }
    if (h >= _top) {
      if (_top < SKIP_LIST_MAX_HEIGHT) {
	h = _top;
	_top++;
      }
      else {
	ASS(_top == SKIP_LIST_MAX_HEIGHT);
	h = _top - 1;
      }
    }
    Node* newNode = allocate(h);
    newNode->value = val;
    // left is a node with a value smaller than that of newNode and having
    // a large enough height.
    // this node is on the left of the inserted one
    Node* left = _left;
    for (;;) {
      Node* next = left->nodes[h];
      if (next == 0) {
	left->nodes[h] = newNode;
	newNode->nodes[h] = 0;
	if (h == 0) {
	  return;
	}
	h--;
	continue;
      }
      // next != 0
      switch (ValueComparator::compare(val,next->value)) 
	{
	case LESS:
	  // the node should be inserted on the left
	  newNode->nodes[h] = next;
	  left->nodes[h] = newNode;
	  if (h == 0) {
	    return;
	  }
	  h--;
	  break;
	
	case GREATER:
	  left = next;
	  break;
	
#if VDEBUG
	default:
	  ASSERTION_VIOLATION;
#endif
	}
    }
  } // SkipList::insert

  /**
   * True if the list is empty.
   * @since 04/05/2006 Bellevue
   */
  inline
  bool isEmpty() const
  {
    return _left->nodes[0] == 0;
  } // SkipList::isEmpty

  /**
   * True if the list is not empty.
   * @since 04/05/2006 Bellevue
   */
  inline
  bool isNonEmpty() const
  {
    return _left->nodes[0] != 0;
  } // SkipList::isNonEmpty

  /**
   * Pop the first element.
   * @since 04/05/2006 Bellevue
   */
  Value pop()
  {
    CALL("SkipList::pop");
    ASS(isNonEmpty());

    // find the height of the first
    Node* node = _left->nodes[0];
    unsigned h;
    for (h = 1;h < _top;h++) {
      if (_left->nodes[h] != node) {
	break;
      }
    }
    // the height of the first node is h-1
    for (unsigned i = 0;i < h;i++) {
      _left->nodes[i] = node->nodes[i];
    }
    Value val = node->value;
    deallocate(node,h-1);
    return val;
  } // SkipList::pop

  /**
   * Remove the value from the list.
   * @since 04/05/2006 Bellevue
   */
  void remove(Value val)
  {
    CALL("SkipList::remove");
    ASS(_top > 0);

    Node* found = 0; // found node
#if VDEBUG
    unsigned foundHeight = 0; // its height
#else
    unsigned foundHeight; // its height
#endif

    Node* left = _left;
    unsigned h = _top-1;
    for (;;) {
      Node* next = left->nodes[h];
      if (next == 0) {
	ASS(h != 0);
	h--;
	continue;
      }
      // next != 0
      switch (ValueComparator::compare(val,next->value)) 
	{
	case LESS:
	  ASS(h != 0);
	  h--;
	  break;
	
	case GREATER:
	  left = next;
	  break;

	case EQUAL:
	  if (! found) {
	    found = next;
	    foundHeight = h;
	  }
	  left->nodes[h] = next->nodes[h];
	  if (h == 0) {
	    ASS(found);
	    deallocate(found,foundHeight);
	    return;
	  }
	  h--;
	  break;
	
#if VDEBUG
	default:
	  ASSERTION_VIOLATION;
#endif
	}
    }
  } // SkipList::remove

  bool find(Value value);
  /**
   * Create a skip list and initialise its left-most node to a node of the
   * maximal possible height.
   * @since 04/05/2006 Bellevue
   */
  SkipList()
    : _left(allocate(SKIP_LIST_MAX_HEIGHT)),
      _top(0)
  {
    CALL("SkipList::SkipList");
    for (int h = SKIP_LIST_MAX_HEIGHT-1;h >= 0;h--) {
      _left->nodes[h] = 0;
    }
  }
  /**
   * Destroy the skip list.
   * @since 04/05/2006 Bellevue
   */
  ~SkipList()
  {
    CALL("SkipList::~SkipList");

    while (isNonEmpty()) {
      pop();
    }
    deallocate(_left,SKIP_LIST_MAX_HEIGHT);
  }
private:
  /** the leftmost node with the dummy key and value */
  Node* _left;
  /** the largest height of nodes + 1 */
  unsigned _top;

  /** allocate node of height h */
  inline
  static Node* allocate(unsigned h)
  {
    CALL("SkipList::allocate");
#if VDEBUG
    void* memory = Allocator::allocator.allocBytes(sizeof(Node)+h*sizeof(Node*),
						   "SkipList::Node");
#else
    void* memory = Allocator::allocator.allocBytes(sizeof(Node)+h*sizeof(Node*));
#endif
    return reinterpret_cast<Node*>(memory);
  }

  /** deallocate node of height h */
  inline
  static void deallocate(Node* node,unsigned h)
  {
    CALL("SkipList::deallocate");
#if VDEBUG
    Allocator::allocator.deallocBytes(node,
				      sizeof(Node)+h*sizeof(Node*),
				      "SkipList::Node");
#else
    Allocator::allocator.deallocBytes(node,sizeof(Node)+h*sizeof(Node*));
#endif
  }
}; // class SkipList


} // namespace Lib
#endif


