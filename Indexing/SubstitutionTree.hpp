/**
 * @file SubstitutionTree.hpp
 * Defines class SubstitutionTree.
 *
 * @since 16/08/2008 flight Sydney-San Francisco
 */

#ifndef __SubstitutionTree__
#define __SubstitutionTree__

#include "../Lib/Stack.hpp"
#include "../Lib/Comparison.hpp"
#include "../Lib/BinaryHeap.hpp"
#include "../Lib/Int.hpp"

#include "../Lib/Map.hpp"
#include "../Lib/List.hpp"

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
  
  void insert(Literal* lit, Clause* cls)
  {
    insert(lit->header(), lit->args(), cls);
  }
  void remove(Literal* lit, Clause* cls)
  {
    remove(lit->header(), lit->args(), cls);
  }

  void insert(TermList* term, Clause* cls)
  {
    ASS(!term->isEmpty());
    if(term->isVar()) {
      ASS(!term->isSpecialVar());
      BindingHeap bh;
      insert(_nodes+_numberOfTopLevelNodes-1, bh, cls);
    } else {
      insert(term->term()->functor(), term->term()->args(), cls);
    }
  }
  void remove(TermList* term, Clause* cls)
  {
    ASS(!term->isEmpty());
    if(term->isVar()) {
      ASS(!term->isSpecialVar());
      BindingHeap bh;
      remove(_nodes+_numberOfTopLevelNodes-1, bh, cls);
    } else {
      remove(term->term()->functor(), term->term()->args(), cls);
    }
  }
  
  void insert(int number,TermList* args,Clause* cls);
  void remove(int number,TermList* args,Clause* cls);

#ifdef VDEBUG
  string toString() const;
  bool isEmpty() const;
#endif
  
private:
  class Node {
  public:
#ifdef VDEBUG
    /** Number of variable at this node, -1 for leaves */
    int var;
    /** True if a leaf node */
    bool isLeaf() const { return var == -1; }
    /** Build a node with a given variable number in it */
    Node(int v) : var(v) {}
#else
    Node(int v) {}
#endif    
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
    class Comparator
    {
    public:
      static Comparison compare(Binding& b1, Binding& b2)
      {
	return Int::compare(b2.var, b1.var);
      }
    };
  }; // class SubstitutionTree::Binding

  typedef BinaryHeap<Binding,Binding::Comparator> BindingHeap;
  typedef Stack<Binding> BindingStack;
  typedef Stack<const TermList*> TermStack;

  void insert(Node** node,BindingHeap& binding,Clause* clause);
  void remove(Node** node,BindingHeap& binding,Clause* clause);
  static bool sameTop(const TermList* ss,const TermList* tt);

  /** Number of top-level nodes */
  int _numberOfTopLevelNodes;
  /** Number of the next variable */
  int _nextVar;
  /** Array of nodes */
  Node** _nodes;
  
  /** Constants are stored here  */
  Map<int,List<Clause*>*,Hash> _constants;
}; // class SubstiutionTree

} // namespace Indexing

#endif
