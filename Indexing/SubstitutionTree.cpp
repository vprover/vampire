/**
 * @file SubstitutionTree.cpp
 * Implements class SubstitutionTree.
 *
 * @since 16/08/2008 flight Sydney-San Francisco
 */

#include "../Kernel/Clause.hpp"
#include "../Kernel/Term.hpp"
#include "../Lib/DHMap.hpp"

#ifdef VDEBUG
#include <iostream>
#include "../Kernel/Signature.hpp"
#include "../Lib/Environment.hpp"
#include "../Lib/Int.hpp"
#include "../Test/Output.hpp"

string SingleTermListToString(const TermList* ts);

#endif

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
  BindingHeap bh;

  int nextVar = 0;
  while (! args->isEmpty()) {
    if (_nextVar <= nextVar) {
      _nextVar = nextVar+1;
    }
    bind.var = nextVar++;
    bind.term = args;
    bh.insert(bind);
    args = args->next();
  }
  
  insert(_nodes+nodeNumber,bh,cls);
} // SubstitutionTree::insert

/**
 * Auxiliary function for substitution tree insertion.
 * @since 16/08/2008 flight Sydney-San Francisco
 */
void SubstitutionTree::insert(Node** node,BindingHeap& bh,Clause* clause)
{
  CALL("SubstitutionTree::insert/3");

 start:
  if (*node == 0) {
    while (!bh.isEmpty()) {
      Binding bind = bh.pop();
      IntermediateNode* inode = new IntermediateNode(bind.var,bind.term,0,0);
      *node = inode;
      node = &(inode->below);
    }
    *node=new Leaf(clause, 0);
    return;
  }

  // *node != 0, extract the next binding to be inserted from the binding map
  if (bh.isEmpty()) {
    Leaf* leaf = static_cast<Leaf*>(*node);
#ifdef VDEBUG
    ASS(leaf->isLeaf());
#endif
    *node = new Leaf(clause,leaf); 
    return;
  }

  // *node != 0 and the binding map is not empty
  IntermediateNode* inode = static_cast<IntermediateNode*>(*node);
#ifdef VDEBUG
  ASS(! inode->isLeaf());
#endif

  Binding bind = bh.top();

#ifdef VDEBUG
  ASS(bind.var == inode->var);
#endif
  
  TermList* tt = bind.term;
  TermList* ss = &inode->term;

  if (ss->sameContent(tt)) {
    bh.pop();
    node = reinterpret_cast<Node**>(&inode->below);
    goto start;
  }

  if (! sameTop(ss,tt)) {
    node = reinterpret_cast<Node**>(&inode->alt);
    goto start;
  }

  // ss is the term in inode, tt is the term to be inserted
  // ss and tt have the same top symbols but are not equal
  // create the common subterm of ss,tt and an alternative node
  bh.pop();
  Stack<TermList*> subterms(64);
  for (;;) {
    if (!ss->sameContent(tt) && sameTop(ss,tt)) {
      // ss and tt have the same tops and are different, so must be non-variables
#ifdef VDEBUG
      ASS(! ss->isVar());
      ASS(! tt->isVar());
#endif

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
    } else {
      if (! sameTop(ss,tt)) {
	int x;
	if(!ss->isSpecialVar()) { 
	  x = _nextVar++;
	  IntermediateNode* newNode = new IntermediateNode(x,ss,0,inode->below);
	  inode->below = newNode;
	  ss->makeSpecialVar(x);
	} else {
	  x=ss->var();
	}
	Binding bind(x,tt);
	bh.insert(bind);
      }
      
      if (subterms.isEmpty()) {
	break;
      }
      tt = subterms.pop();
      ss = subterms.pop();
      if (! ss->next()->isEmpty()) {
	subterms.push(ss->next());
	subterms.push(tt->next());
      }
    }
  }
  ASS(inode->below);
#ifdef VDEBUG
  ASS(!inode->below->isLeaf());
#endif
  node = &inode->below;
  
  goto start;
} // // SubstitutionTree::insert

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
  BindingHeap bh;

  int nextVar = 0;
  while (! args->isEmpty()) {
    ASS(_nextVar > nextVar);

    bind.var = nextVar++;
    bind.term = args;
    bh.insert(bind);
    args = args->next();
  }

  remove(_nodes+nodeNumber,bh,cls);
} // remove

/*
 * Remove a clause from the substitution tree.
 * @since 16/08/2008 flight San Francisco-Seattle
 */
void SubstitutionTree::remove(Node** pnode,BindingHeap& bh,Clause* clause)
{
  CALL("SubstitutionTree::remove-2");
  
  Node* node=*pnode;

  ASS(node);

  Stack<Node*> history(1000);

  while (! bh.isEmpty()) {

#ifdef VDEBUG
    ASS (! node->isLeaf());
#endif

    Binding bind = bh.pop();
    TermList* t = bind.term;
    
  node_check:
    IntermediateNode* inode = static_cast<IntermediateNode*>(node);
#ifdef VDEBUG
    ASS(inode->var == bind.var);
#endif
    TermList s = inode->term;
    if (s.content() == t->content()) {
      history.push(node);
      node = inode->below;
      continue;
    }
    if (! sameTop(&s,t)) {
      //we dont have to remember what was before, as nothing below this node
      //will be deleted
      history.reset();
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
	bh.insert(b);
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
#ifdef VDEBUG
  ASS (node->isLeaf());
#endif

  //younger brothers are closer to the parent
  //(only if they're leafs. for intermediate nodes, younger are further)
  Leaf* closestYoungerBrother = 0;
  Leaf* lnode = static_cast<Leaf*>(node);
  while (lnode && lnode->clause!=clause) {
    closestYoungerBrother = lnode;
    lnode = lnode->next;
  }
  if (!lnode) { //clause is not here
    return;
  }

  //Now let's remove the leaf and all unnecessary intermediate nodes 
  
  if (closestYoungerBrother) {
    closestYoungerBrother->next = lnode->next;
    delete lnode;
    return;
  }
  if(history.isEmpty()) {
    //this "tree" contains only leaves and node is the first of them
    ASS(*pnode==node);
    *pnode=lnode->next;
    delete lnode;
    return;
  }
  IntermediateNode* previous = static_cast<IntermediateNode*>(history.pop());
  if (lnode->next) {
    previous->below = lnode->next;
    delete lnode;
    return;
  }
  //removed clause was the only child
  delete lnode;
  while (! history.isEmpty()) {
    IntermediateNode* inode = previous;
    previous = static_cast<IntermediateNode*>(history.pop());
    if (inode==previous->alt) {
      previous->alt = inode->alt;
      delete inode;
      return;
    }
    ASS(inode==previous->below);
    if (inode->alt) {
      previous->below = inode->alt;
      delete inode;
      return;
    }
    delete inode;
  }
  
  ASS(history.isEmpty());
  //before we delete the node that the pointer from _nodes array points to,
  //we have to redirect the pointer to the next node
  *pnode=previous->alt;
  delete previous;
  
} // SubstitutionTree::remove


#if VDEBUG

/**
 * Get string representation of just the header of given term.
 * 
 * This us useful when there's something wrong with the term and
 * Test::Output::toString causes segmentation faults.
 */
string SingleTermListToString(const TermList* ts)
{
  if(ts->isOrdinaryVar()) {
    return string("X")+Int::toString(ts->var());
  } else if(ts->isSpecialVar()) {
    return string("S")+Int::toString(ts->var());
  } else if(ts->isEmpty()) {
    return "EMPTY";
  }
  
  //term is REF
  const Term* term=ts->term();
  return Test::Output::toString(term);
}

/**
 * Return the string representation of the tree
 */
string SubstitutionTree::toString() const
{
  CALL("SubstitutionTree::toString");

  string res;
  
  for(int tli=0;tli<_numberOfTopLevelNodes;tli++) {
    res+=Int::toString(tli);
    res+=":\n";
    
    Stack<int> indentStack(10);
    Stack<Node*> stack(10);
    stack.push(_nodes[tli]);
    indentStack.push(1);
    
    while(stack.isNonEmpty()) {
      Node* node=stack.pop();
      int indent=indentStack.pop();

      if(!node) {
	continue;
      }
      
      for(int indCnt=0;indCnt<indent*2;indCnt++) {
	res+=" ";
      }

      if(node->isLeaf()) {
	Leaf* lnode = static_cast<Leaf*>(node);
	stack.push(lnode->next);
	indentStack.push(indent);
	res+="L: ";
	res+=Test::Output::toString(lnode->clause);
      } else {
	IntermediateNode* inode = static_cast<IntermediateNode*>(node);
	stack.push(inode->alt);
	indentStack.push(indent);
	stack.push(inode->below);
	indentStack.push(indent+1);
	res+="I: S";
	res+=Int::toString(inode->var);
	res+=" --> ";
	res+=SingleTermListToString(&inode->term);
      }
      res+="\n";
    }
  }
  return res;
} // DoubleSubstitution::toString()


#endif

