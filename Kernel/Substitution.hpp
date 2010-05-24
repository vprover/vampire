/**
 * @file Substitution.hpp
 * Defines class Substitution.
 *
 * @since 08/07/2007 Manchester, flight Manchester-Cork
 * @since 30/12/2007 Manchester, reimplemented from scratch using a skip list
 * like structure
 */

#ifndef __Substitution__
#define __Substitution__

#if VDEBUG
#  include <string>
using namespace std;
#endif

#include "Lib/Random.hpp"
#include "Lib/Allocator.hpp"
#include "Lib/Environment.hpp"

#include "Term.hpp"

using namespace Lib;

#define SUBST_MAX_HEIGHT 31

namespace Kernel {

/**
 * The class Substitution implementing substitutions.
 * @since 30/12/2007 Manchester
 */
class Substitution
{
public:
  Substitution() : _height(-1) {}
  ~Substitution();
  void bind(int v,Term* t);
  void bind(int v,TermList t);
  TermList* bound(int var) const;
  void unbind(int var);
#if VDEBUG
  string toString() const;
#endif
private:
  /** Nodes in the skip list */
  class Node {
  public:
    /** Variable at this node */
    int var;
    /** Term at this node, must be different from the variable */
    TermList term;
    /** Links to other nodes on the right, can be of any length */
    Node* nodes[1];
  };
  /** This class is just to have the leftmost dummy node of sufficient
   * size */
  class LargeNode
    : public Node
  {
  private:
    Node* _[SUBST_MAX_HEIGHT];
  };
  /** Height of the leftmost node minus 1 */
  int _height;
  /** the leftmost node with the dummy key and value */
  LargeNode _left;
}; // class Substitution


}

#endif // __Substitution__

