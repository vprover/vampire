/**
 * @file Substitution.cpp
 * Implements class Substitution.
 * @since 28/12/2007 Manchester, implemented from scratch
 */

#if VDEBUG
#  include "../Lib/Int.hpp"
#  include "Term.hpp"
#endif

#include "Substitution.hpp"

using namespace Kernel;

/** Temporary!!! */
Substitution::~Substitution ()
{
}

/**
 * Bind @b v to @b t.
 * @pre @b v must previously be unbound
 */
void Substitution::bind(int v,Term* t)
{
  TermList ts;
  ts.setTerm(t);
  bind(v,ts);
}

/**
 * Bind @b v to @b t.
 * @pre @b v must previously be unbound
 */
void Substitution::bind(int v,TermList t)
{
  CALL("Substitution::bind");

  // select a random height between 0 and top
  int h = 0;
  while (Random::getBit()) {
    h++;
  }
  if (h > _height) {
    if (_height < SUBST_MAX_HEIGHT) {
      _height++;
    }
    h = _height;
    _left.nodes[h] = 0;
  }
  void* mem = ALLOC_KNOWN(sizeof(Node)+h*sizeof(Node*),
			  "Substitution::Node");
  Node* newNode = reinterpret_cast<Node*>(mem);
  newNode->var = v;
  newNode->term = t;

  // left is a node with a value smaller than that of newNode and having
  // a large enough height.
  // this node is on the left of the inserted one
  Node* left = &_left;
  // lh is the height on which we search for the next node
  int lh = _height;
  for (;;) {
    Node* next = left->nodes[lh];
    if (next == 0 || v < next->var) {
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
    ASS(v > next->var);
    left = next;
  }
} // Substitution::bind

/**
 * Remove the binding for @b v from the substitution.
 * @pre @b v must previously be bound
 * @since 04/05/2006 Bellevue
 * @since 30/12/2007 Manchester
 */
void Substitution::unbind(int v)
{
  CALL("Substitution::unbind");
  ASS(_height >= 0);

  int h = _height;
  Node* left = &_left;

  for (;;) {
    Node* next = left->nodes[h];
    if (next == 0 || next->var > v) {
      ASS(h != 0);
      h--;
      continue;
    }
    // next != 0
    if (next->var < v) {
      left = next;
      continue;
    }
    int height = h;
    // found, first change the links going to next
    for (;;) {
      left->nodes[h] = next->nodes[h];
      if (h == 0) {
	break;
      }
      h--;
      while (left->nodes[h] != next) {
	left = left->nodes[h];
      }
    }
    // deallocate the node
    DEALLOC_KNOWN(next,
		  sizeof(Node)+height*sizeof(Node*),
		  "Substitution::Node");
    return;
  }
} // Substitution::unbind

/**
 * Return the binding for @b v.
 * @since 30/12/2007 Manchester
 */
TermList* Substitution::bound(int v) const
{
  CALL("Substitution::bound");

  int h = _height;
  const Node* left = &_left;
  while (h >= 0) {
    Node* next = left->nodes[h];
    if (next == 0 || next->var > v) {
      h--;
      continue;
    }
    if (next->var == v) {
      return &next->term;
    }
    left = next;
  }
  return 0;
} // Substitution::bound


#if VDEBUG
// string Substitution::toString() const
// {
//   string result("[");
//   if (_height >= 0) {
//     bool first = true;
//     for (const Node* node = _left.nodes[0]; node; node=node->nodes[0]) {
//       if (first) {
// 	first = false;
//       }
//       else {
// 	result += ',';
//       }
//       result += string("X") + Int::toString(node->var) +
//                 "->" + node->term->toString();
//     }
//   }
//   result += ']';
//   return result;
// } // Substitution::toString()
#endif
