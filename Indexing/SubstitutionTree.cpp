/**
 * @file SubstitutionTree.cpp
 * Implements class SubstitutionTree.
 *
 * @since 16/08/2008 flight Sydney-San Francisco
 */

#include "../Kernel/Clause.hpp"
#include "../Kernel/Term.hpp"
#include "SubstitutionTree.hpp"

using namespace Indexing;

/**
 * Initialise the substitution tree.
 * @since 16/08/2008 flight Sydney-San Francisco
 */
SubstitutionTree::SubstitutionTree(int nodes)
  : _numberOfTopLevelNodes(nodes),
    _nextVar(0)
{
  CALL("SubstitutionTree::SubstitutionTree");
  ASS(nodes > 0);

  _nodes = new(ALLOC_KNOWN(nodes*sizeof(Node*),"SubstitutionTree::Node"))
                Node*[nodes];
  for (int i = nodes-1;i >= 0;i--) {
    _nodes[i] = 0;
  }
} // SubstitutionTree::SubstitutionTree

/**
 * Destroy the substitution tree.
 * @warning does not destroy nodes yet
 * @since 16/08/2008 flight Sydney-San Francisco
 */
SubstitutionTree::~SubstitutionTree()
{
  CALL("SubstitutionTree::~SubstitutionTree");

  DEALLOC_KNOWN(_nodes,
		_numberOfTopLevelNodes*sizeof(Node*),
		"SubstitutionTree::Node");
} // SubstitutionTree::~SubstitutionTree

/**
 * Insert term arguments to the tree.
 * @param nodeNumber the number of the node in the tree
 * @param args the list of arguments to be inserted
 * @param cls the clause to be stored at the leaf.
 * @since 16/08/2008 flight Sydney-San Francisco
 */
void SubstitutionTree::insert(int nodeNumber,TermList* args,Clause* cls)
{
  CALL("SubstitutionTree::insert");
  ASS(nodeNumber < _numberOfTopLevelNodes);
  ASS(nodeNumber >= 0);

  Binding bind;
  BindingStack stack(64);

  int nextVar = 0;
  while (! args->isEmpty()) {
    if (_nextVar <= nextVar) {
      _nextVar = nextVar+1;
    }
    bind.var = nextVar++;
    bind.term = args;
    stack.push(bind);
    args = args->next();
  }
  insert(_nodes+nodeNumber,stack,cls);
} // SubstitutionTree::insert

/**
 * Auxiliary function for substitution tree insertion.
 * @since 16/08/2008 flight Sydney-San Francisco
 */
void SubstitutionTree::insert(Node** node,BindingStack& stack,Clause* clause)
{
  CALL("SubstitutionTree::insert/3");
 start:
  if (*node == 0) {
    while (! stack.isEmpty()) {
      Binding bind = stack.pop();
      IntermediateNode* inode = new IntermediateNode(bind.var,bind.term,0,0);
      *node = inode;
      node = &(inode->below);
    }
    return;
  }

  // *node != 0, extract the next binding to be inserted from the stack
  if (stack.isEmpty()) {
    Leaf* leaf = static_cast<Leaf*>(*node);
    ASS(leaf->isLeaf());
    *node = new Leaf(clause,leaf); 
    return;
  }

  // *node != 0 and the stack is not empty
  IntermediateNode* inode = static_cast<IntermediateNode*>(*node);
  ASS(! inode->isLeaf());

  Binding bind = stack.top();
  TermList* tt = bind.term;

  TermList* ss = &inode->term;
  int vs = inode->var;

  if (ss->sameContent(tt)) {
    stack.pop();
    node = reinterpret_cast<Node**>(&inode->below);
    goto start;
  }

  ASS(vs == bind.var);

  if (! sameTop(ss,tt)) {
    node = reinterpret_cast<Node**>(&inode->alt);
    goto start;
  }

  // ss is the term in inode, tt is the term to be inserted
  // ss and tt have the same top symbols but are not equal
  // create the common subterm of ss,tt and an alternative node
  stack.pop();
  Stack<TermList*> subterms(64);
  for (;;) {
    if (ss->sameContent(tt)) {
      if (subterms.isEmpty()) {
	goto start;
      }
      tt = subterms.pop();
      ss = subterms.pop();
      if (! ss->next()->isEmpty()) {
	subterms.push(ss->next());
	subterms.push(tt->next());
      }
      continue;
    }

    // ss and tt are different
    if (! sameTop(ss,tt)) {
      int x = _nextVar++;
      IntermediateNode* newNode = new IntermediateNode(x,ss,0,inode->below);
      inode->below = newNode;
      ss->makeSpecialVar(x);
      Binding bind(x,tt);
      stack.push(bind);
      node = reinterpret_cast<Node**>(&inode->alt);
      break;
    }

    // ss and tt have the same tops and so must be non-variables
    ASS(! ss->isVar());
    ASS(! tt->isVar());

    Term* s = ss->term();
    Term* t = tt->term();

    ASS(s->arity() > 0);
    ASS(s->functor() == t->functor());

    if (s->shared()) {
      // create a shallow copy of s
      s = Term::createNonShared(s,s->args());
      ss->setTerm(s);
    }

    ss = s->args();
    tt = t->args();
    if (ss->next()->isEmpty()) {
      continue;
    }
    subterms.push(ss->next());
    subterms.push(tt->next());
  }
} // 

/**
 * Return true if @b ss and @b tt have the same top symbols, that is,
 * either both are the same variable or both are complex terms with the
 * same function symbol. 
 * @since 16/08/2008 flight Sydney-San Francisco
 */
bool SubstitutionTree::sameTop(const TermList* ss,const TermList* tt)
{
  if (ss->isVar()) {
    return ss->sameContent(tt);
  }
  if (tt->isVar()) {
    return false;
  }
  return ss->term()->functor() == tt->term()->functor();
}

/*
 * Remove a clause from the substitution tree.
 * @since 16/08/2008 flight San Francisco-Seattle
 */
void SubstitutionTree::remove(int nodeNumber,TermList* args,Clause* cls)
{
  CALL("SubstitutionTree::remove-1");
  ASS(nodeNumber < _numberOfTopLevelNodes);
  ASS(nodeNumber >= 0);

  Binding bind;
  BindingStack stack(64);

  int nextVar = 0;
  while (! args->isEmpty()) {
    ASS(_nextVar > nextVar);

    bind.var = nextVar++;
    bind.term = args;
    stack.push(bind);
    args = args->next();
  }
  remove(_nodes[nodeNumber],stack,cls);
} // remove

/*
 * Remove a clause from the substitution tree.
 * @since 16/08/2008 flight San Francisco-Seattle
 */
void SubstitutionTree::remove(Node* node,BindingStack& bstack,Clause* clause)
{
  CALL("SubstitutionTree::remove-2");
  ASS(node);

  cout << "Removing clause " << clause->toString() << "\n";
  Stack<Node*> history(1000);

  while (! bstack.isEmpty()) {
    ASS (! node->isLeaf());

    Binding bind = bstack.pop();
    int var = bind.var;
    TermList* t = bind.term;

  node_check:
    IntermediateNode* inode = static_cast<IntermediateNode*>(node);
    ASS(inode->var == var);
    TermList s = inode->term;
    if (s.content() == t->content()) {
      history.push(node);
      node = inode->below;
      continue;
    }
    if (! sameTop(&s,t)) {
      history.push(node);
      node = inode->alt;
      goto node_check;
    }
    ASS(! s.isVar());
    const TermList* ss = s.term()->args();
    if (ss->isEmpty()) {
      ASS(t->term()->args()->isEmpty());
      continue;
    }
    // computing the disagreement set of the two terms
    TermStack subterms(120);
    subterms.push(ss);
    subterms.push(t->term()->args());
    while (! subterms.isEmpty()) {
      const TermList* tt = subterms.pop();
      ss = subterms.pop();
      if (tt->next()->isEmpty()) {
	ASS(ss->next()->isEmpty());
      }
      else {
	subterms.push(ss->next());
	subterms.push(tt->next());
      }
      if (ss->content() == tt->content()) {
	continue;
      }
      if (ss->isVar()) {
	ASS(ss->isSpecialVar());
	Binding b(ss->var(),const_cast<TermList*>(tt));
	bstack.push(b);
	continue;
      }
      ASS(! t->isVar());
      ASS(ss->term()->functor() == tt->term()->functor());
      ss = ss->term()->args();
      if (! ss->isEmpty()) {
	ASS(! tt->term()->args()->isEmpty());
	subterms.push(ss);
	subterms.push(tt->term()->args());
      }
    }
    history.push(node);
    node = inode->below;
  }
  ASS (node->isLeaf());
  cout << "Found!\n";
} // SubstitutionTree::remove

