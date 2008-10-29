/**
 * @file SubstitutionTree.hpp
 * Defines class SubstitutionTree.
 *
 * @since 16/08/2008 flight Sydney-San Francisco
 */

#ifndef __SubstitutionTree__
#define __SubstitutionTree__

#include "../Lib/Stack.hpp"

namespace Kernel {
  class TermList;
  class Clause;
};

using namespace std;
using namespace Lib;
using namespace Kernel;

namespace Indexing {

/**
 * Class of substitution trees. In fact, contains an array of substitution
 * trees.
 * @since 16/08/2008 flight Sydney-San Francisco
 */
class SubstitutionTree
{
private:
public:
  SubstitutionTree(int nodes);
  ~SubstitutionTree();
  void insert(int number,TermList* args,Clause* cls);
  void remove(int number,TermList* args,Clause* cls);

private:
  class Node {
  public:
    /** Number of variable at this node, -1 for leaves */
    int var;
    /** True if a leaf node */
    bool isLeaf() const { return var == -1; }
    /** Build a node with a given variable number in it */
    Node(int v) : var(v) {}
  };

  class IntermediateNode
    : public Node
  {
  public:
    /** term at this node */
    TermList term;
    /** alternative node */
    IntermediateNode* alt;
    /** node below */
    Node* below;
    /** Build a new intermediate node */
    IntermediateNode(int var,TermList* ts,
		     IntermediateNode* alternative,Node* bel)
      : Node(var),
	term(*ts),
	alt(alternative),
	below(bel)
    {}
  }; // class SubstitutionTree::Node

  class Leaf
    : public Node
  {
  public:
    /** The clause at this node */
    Clause* clause;
    /** next leaf */
    Leaf* next;
    /** Build a new leaf */
    Leaf(Clause* cls, Leaf* nxt)
      : Node(-1),
	clause(cls),
	next(nxt)
    {}
  };

  class Binding {
  public:
    /** Number of the variable at this node */
    int var;
    /** term at this node */
    TermList* term;
    /** Create new binding */
    Binding(int v,TermList* t) : var(v), term(t) {}
    /** Create uninitialised binding */
    Binding() {}
  }; // class SubstitutionTree::Binding

  typedef Stack<Binding> BindingStack;
  typedef Stack<const TermList*> TermStack;

  void insert(Node** node,BindingStack& binding,Clause* clause);
  void remove(Node* node,BindingStack& binding,Clause* clause);
  static bool sameTop(const TermList* ss,const TermList* tt);

  /** Number of top-level nodes */
  int _numberOfTopLevelNodes;
  /** Number of the next variable */
  int _nextVar;
  /** Array of nodes */
  Node** _nodes;
}; // class SubstiutionTree

} // namespace Indexing

#endif
