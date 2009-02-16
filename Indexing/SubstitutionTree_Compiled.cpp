/**
 * @file SubstitutionTree_Compiled.cpp
 * Implements class SubstitutionTree::CompiledTree.
 */

#include "SubstitutionTree.hpp"

#include "../Lib/MapToLIFO.hpp"
#include "../Lib/Environment.hpp"
#include "../Lib/Timer.hpp"
#include "../Lib/DHMultiset.hpp"

#include "../Kernel/Signature.hpp"

#include <iostream>

namespace Indexing {

using namespace std;
using namespace Lib;
using namespace Kernel;

template<typename T>
struct Converter
{
  inline
  Converter(T obj) : obj(obj) {}
  inline
  Converter(size_t num) : num(num) {}
  inline
  union {
    T obj;
    size_t num;
  };
};
template<typename T>
size_t toSizeT(T obj)
{
  return Converter<T>(obj).num;
}
template<typename T>
T fromSizeT(size_t num)
{
  return Converter<T>(num).obj;
}

class SubstitutionTree::CompiledTree
{
public:
  typedef DHMultiset<Node*, PtrIdentityHash> NodeSet;

  CompiledTree(SubstitutionTree *parent, IntermediateNode* root, unsigned initBindingCount)
  : _ovBindingsSize(0), _ovBindings(0)
  {
    CALL("SubstitutionTree::CompiledTree::CompiledTree");

    size_t maxCodeSize;
    size_t maxTreeDepth;
    NodeSet unusedVarBindingNodes;
    getTreeStats(root,maxCodeSize, maxTreeDepth, unusedVarBindingNodes);
    _svBindings=static_cast<TermList*>(
	    ALLOC_UNKNOWN(maxTreeDepth*sizeof(TermList), "SubstitutionTree::CompiledTree::_svBindings"));
    _code=static_cast<char*>(
	    ALLOC_UNKNOWN(maxCodeSize, "SubstitutionTree::CompiledTree::_code"));
#if VDEBUG
    _afterLastAllocatedCode=_code+maxCodeSize;
    _afterLastAllocatedSVBinding=_svBindings+maxTreeDepth;
#endif

    OP_MATCH_TERM=toSizeT(&CompiledTree::opMatchTerm);
    OP_MATCH_GROUND_TERM=toSizeT(&CompiledTree::opMatchGroundTerm);
    OP_MATCH_NEW_VAR=toSizeT(&CompiledTree::opMatchNewVar);
    OP_MATCH_ENCOUNTERED_VAR=toSizeT(&CompiledTree::opMatchEncounteredVar);
    OP_SKIP_IRRELEVANT_CHILDREN=toSizeT(&CompiledTree::opSkipIrrelevantChildren);
    OP_LEAF=toSizeT(&CompiledTree::opLeaf);
    OP_FAIL=toSizeT(&CompiledTree::opFail);

    compileTree(root, initBindingCount, unusedVarBindingNodes);
  }
  ~CompiledTree()
  {
    CALL("SubstitutionTree::CompiledTree::~CompiledTree");

    DEALLOC_UNKNOWN(_svBindings, "SubstitutionTree::CompiledTree::_svBindings");
    if(_ovBindings) {
      DEALLOC_UNKNOWN(_ovBindings, "SubstitutionTree::CompiledTree::_ovBindings");
    }
    DEALLOC_UNKNOWN(_code, "SubstitutionTree::CompiledTree::_code");
  }

  void initForRetrieval(Term* query)
  {
    CALL("SubstitutionTree::CompiledTree::initForRetrieval");

    ASS(query->shared());
    _addr=_code;
    if(!_ovBindings || _ovBindingsSize<query->weight()) {
      if(_ovBindings) {
        DEALLOC_UNKNOWN(_ovBindings, "SubstitutionTree::CompiledTree::_ovBindings");
      }
      _ovBindingsSize=min(max(8u,_ovBindingsSize*2),query->weight());
      _ovBindings=static_cast<TermList*>(
	      ALLOC_UNKNOWN(_ovBindingsSize*sizeof(TermList*),"SubstitutionTree::CompiledTree::_ovBindings"));
    }
    _maxVar=query->weight()-1;
  }

  Leaf* getNextLeaf()
  {
    run();
    return _leaf;
  }

  static size_t getSizeCost(Node* n)
  {
    size_t longCnt=5;

    if(n->term.isTerm()) {
      longCnt+=2;
    }

    if(n->isLeaf()) {
      longCnt+=2;
    } else {
      longCnt+=4;
    }
    return longCnt*sizeof(void*);
  }
  static void getTreeStats(IntermediateNode* root, size_t& codeSizeUpperBound,
      size_t& maxDepth, NodeSet& unusedVarBindingNodes)
  {
    CALL("SubstitutionTree::CompiledTree::getMaxTreeSize");

    static Stack<NodeIterator> alts(32);
    alts.reset();

    typedef DHMap<unsigned,Node*,IdentityHash<unsigned> > Var2NodeMap;
    Var2NodeMap unusedBoundVars;

    size_t sz=40;

    maxDepth=2;
    alts.push(root->allChildren());
    for(;;) {
      while(alts.isNonEmpty()&&!alts.top().hasNext()) {
	alts.pop();
      }
      if(alts.isEmpty()) {
	break;
      }
      Node* curr=*alts.top().next();
      if(curr->term.isOrdinaryVar()) {
	unsigned var=curr->term.var()&~NEW_VARIABLE_MARK;
	if(curr->term.var()!=var) {
	  if(unusedBoundVars.find(var)) {
	    unusedVarBindingNodes.insert(unusedBoundVars.get(var));
	  }
	  unusedBoundVars.set(var, curr);
	} else {
	  if(unusedBoundVars.find(var)) {
	    unusedBoundVars.remove(var);
	  }
	}
      } else {
	Term::VariableIterator vit(curr->term.term());
	while(vit.hasNext()) {
	  TermList vt=vit.next();
	  if(vt.isOrdinaryVar()) {
	    unsigned var=vt.var();
	    if(var&NEW_VARIABLE_MARK) {
	      var&=~NEW_VARIABLE_MARK;
	      if(unusedBoundVars.find(var)) {
		unusedVarBindingNodes.insert(unusedBoundVars.get(var));
		unusedBoundVars.remove(var);
	      }
	    } else if(unusedBoundVars.find(var)) {
	      unusedBoundVars.remove(var);
	    }
	  }
	}
      }


      ASS(curr);
      ASSERT_VALID(*curr);
      if(!curr->isLeaf()) {
	alts.push(static_cast<IntermediateNode*>(curr)->allChildren());
	if(alts.size()>maxDepth) {
	  maxDepth=alts.size();
	}
      }
      sz+=getSizeCost(curr);
    }

    Var2NodeMap::Iterator vnit(unusedBoundVars);
    while(vnit.hasNext()) {
      unusedVarBindingNodes.insert(vnit.next());
    }

    maxDepth++;
    codeSizeUpperBound=sz;
  }
  inline
  static void storeLong(char*& addr, size_t num)
  {
    *reinterpret_cast<size_t*>(addr)=num;
    shiftByLong(addr);
  }
  inline
  static void storePtr(char*& addr, void* ptr)
  {
    *reinterpret_cast<void**>(addr)=ptr;
    shiftByLong(addr);
  }
  inline
  static size_t getLong(char* addr)
  {
    return *reinterpret_cast<size_t*>(addr);
  }
  inline
  static size_t readLong(char*& addr)
  {
    size_t res=getLong(addr);
    shiftByLong(addr);
    return res;
  }
  inline
  static void* getPtr(char* addr)
  {
    return *reinterpret_cast<void**>(addr);
  }
  inline
  static void* readPtr(char*& addr)
  {
    void* res=getPtr(addr);
    shiftByLong(addr);
    return res;
  }
  inline
  static char* getAddr(char* addr)
  {
    return *reinterpret_cast<char**>(addr);
  }
  inline
  static char* readAddr(char*& addr)
  {
    char* res=getAddr(addr);
    shiftByLong(addr);
    return res;
  }
  inline
  static void shiftByLong(char*& addr)
  {
    addr+=sizeof(void*);
  }

  char* storeNode(char*& addr, Node* node, unsigned specVarOfs, unsigned specVarCnt,
      NodeSet& unusedVarBindingNodes)
  {
    CALL("SubstitutionTree::CompiledTree::storeNode");
    char* failAddrPtr;
    if(unusedVarBindingNodes.find(node)) {
      ASS(node->term.isVar());
      ASS(node->term.var()&NEW_VARIABLE_MARK);
      failAddrPtr=0;
    } else {
      TermList nodeTerm=node->term;
      if(nodeTerm.isVar()) {
	bool marked=nodeTerm.var()&NEW_VARIABLE_MARK;
	if(marked) {
	  storeLong(addr, OP_MATCH_NEW_VAR);
	} else {
	  storeLong(addr, OP_MATCH_ENCOUNTERED_VAR);
	}
	storePtr(addr, &_svBindings[specVarOfs]);
	storeLong(addr, nodeTerm.var()&~NEW_VARIABLE_MARK);
      } else {
	ASS(nodeTerm.isTerm());
	if(nodeTerm.term()->shared()&&nodeTerm.term()->ground()) {
	  storeLong(addr, OP_MATCH_GROUND_TERM);
	  storePtr(addr, &_svBindings[specVarOfs]);
	  storeLong(addr, nodeTerm.content());
	} else {
	  storeLong(addr, OP_MATCH_TERM);
	  storePtr(addr, &_svBindings[specVarCnt]);
	  storePtr(addr, &_svBindings[specVarOfs]);
	  storeLong(addr, nodeTerm.content());
	}
      }
      failAddrPtr=addr;
      shiftByLong(addr);
    }

    if(node->isLeaf()) {
      storeLong(addr, OP_LEAF);
      storePtr(addr, node);
    }

    return failAddrPtr;
  }
  void storeFail(char*& addr)
  {
    storeLong(addr, OP_FAIL);
  }

  typedef DHMap<unsigned, unsigned, IdentityHash<unsigned> > SV2OfsMap;
  typedef MapToLIFO<Node*,char*,PtrIdentityHash> ForwardAddressTargetStore;

  struct TermNodeComparator
  {
    static Comparison compare(Node* n1, Node* n2)
    {
      return Int::compare(n1->term.term()->functor(), n2->term.term()->functor());
    }
  };
  char* storeChildSkipOp(char*& addr, IntermediateNode* inode, unsigned specVarOfs,
      NodeList*& nodesOrdered, Node*& firstVarNode,
      ForwardAddressTargetStore& fwAddressTargets)
  {
    CALL("SubstitutionTree::CompiledTree::storeChildSkipOp");
    ASS_G(inode->size(),0);
    BinaryHeap<Node*,TermNodeComparator> termNodes;
    nodesOrdered=0;
    firstVarNode=0;
    NodeIterator chit=inode->allChildren();
    while(chit.hasNext()) {
      Node* n=*chit.next();
      if(n->term.isTerm()) {
	termNodes.insert(n);
      } else {
	NodeList::push(n, nodesOrdered);

	//First in the sense of nodesOrdered list, so we have to update
	//it with each variable node pushed.
	firstVarNode=n;
      }
    }
    if(termNodes.size()>0) {
      storeLong(addr, OP_SKIP_IRRELEVANT_CHILDREN);
      storePtr(addr, &_svBindings[specVarOfs]);
      char* res;
      if(firstVarNode) {
	//register point where pointer to first variable node should be stored
	fwAddressTargets.pushToKey(firstVarNode, addr);
	shiftByLong(addr);
	res=0;
      } else {
	//there are no variable nodes, so we'll let caller decide where to go
	res=addr;
	shiftByLong(addr);
      }
      storeLong(addr, termNodes.size());
      while(!termNodes.isEmpty()) {
	Node* n=termNodes.pop();
	NodeList::push(n, nodesOrdered);
	storeLong(addr, n->term.term()->functor());

	//register point where pointer to this node should be stored
	fwAddressTargets.pushToKey(n, addr);
	shiftByLong(addr);
      }
      return res;
    }

    return 0;
  }


  void fillInFailPoints(ForwardAddressTargetStore& tgts, Node* node, char* point)
  {
    CALL("SubstitutionTree::CompiledTree::fillInFailPoints");

    while(!tgts.isKeyEmpty(node)) {
      char* tgt=tgts.popFromKey(node);
      *reinterpret_cast<char**>(tgt)=point;
    }
  }

  void enterNode(char*& addr, IntermediateNode* inode, Node* failNode,
      Stack<Node*>& nexts, Stack<NodeList*>& alts, Stack<unsigned>& specVars,
      SV2OfsMap& specVarOffsets, ForwardAddressTargetStore& fwAddressTargets)
  {
    CALL("SubstitutionTree::CompiledTree::enterNode");
    ASS_EQ(nexts.top(),failNode);

    Node* firstVarChild=0;
    alts.push(0);
    specVars.push(inode->childVar);
    char* failPntTgt=storeChildSkipOp(addr,inode,specVarOffsets.get(inode->childVar),
	alts.top(),firstVarChild,fwAddressTargets);
    //no node should be empty
    ASS(alts.top());
    if(failPntTgt) {
      fwAddressTargets.pushToKey(failNode, failPntTgt);
    }

    if(firstVarChild) {
      nexts.push(firstVarChild);
    }
  }

  void compileTree(IntermediateNode* root, unsigned initBindingCount,
      NodeSet& unusedVarBindingNodes)
  {
    CALL("SubstitutionTree::CompiledTree::compileTree");
    Stack<Node*> nexts(32);
    static Stack<NodeList*> alts(32);
    static Stack<unsigned> specVars(32);
    static Stack<unsigned> nextSpecVarOffsets(32);
    nexts.reset();
    alts.reset();
    specVars.reset();
    nextSpecVarOffsets.reset();

    unsigned nextSpecVarOfs=initBindingCount;
    static SV2OfsMap specVarOffsets;
    for(unsigned i=0;i<initBindingCount;i++) {
      specVarOffsets.set(i,i);
    }

    ForwardAddressTargetStore fwAddressTargets;
    ASS(root->term.isEmpty());

    char* addr=_code;
    nexts.push(0);

    nextSpecVarOffsets.push(nextSpecVarOfs);

    enterNode(addr,root,0,nexts,alts,specVars,specVarOffsets,fwAddressTargets);

    do {
      Node* curr=NodeList::pop(alts.top());
      unsigned specVarOfs=specVarOffsets.get(specVars.top());
      nextSpecVarOfs=nextSpecVarOffsets.top();

      if(nexts.top()==curr) {
	NodeList* laterSibilings=alts.top();
	if(laterSibilings) {
	  nexts.setTop(laterSibilings->head());
	} else {
	  nexts.pop();
	}
      }
      Node* failPnt=nexts.top();

      while(alts.isNonEmpty() && alts.top()==0) {
	alts.pop();
	specVars.pop();
	nextSpecVarOffsets.pop();
      }

      //fill in address of this node, where it's needed as a fail point
      fillInFailPoints(fwAddressTargets, curr, addr);

      char* failPntTgt=storeNode(addr,curr,specVarOfs,nextSpecVarOfs,unusedVarBindingNodes);

      if(failPntTgt) {
	//register point where fail point for this node should be stored
	fwAddressTargets.pushToKey(failPnt, failPntTgt);
      }

      if(curr->term.isTerm() && !curr->term.term()->shared()) {
	Term::VariableIterator vit(curr->term.term());
	while(vit.hasNext()) {
	  TermList v=vit.next();
	  if(v.isSpecialVar()) {
	    specVarOffsets.set(v.var(),nextSpecVarOfs++);
	  }
	}
      }

      if(!curr->isLeaf()) {
	IntermediateNode* inode=static_cast<IntermediateNode*>(curr);
	enterNode(addr,inode,failPnt,nexts,alts,specVars,specVarOffsets,fwAddressTargets);
	nextSpecVarOffsets.push(nextSpecVarOfs);
      }
    } while(!alts.isEmpty());
    fillInFailPoints(fwAddressTargets, 0, addr);
    storeFail(addr);
#if VDEBUG
    ASS_EQ((addr-_code)%8,0);
    ASS_LE((void*)addr,(void*)_afterLastAllocatedCode);
    _afterLastCode=addr;
#endif
  }

  void run()
  {
    _addr=_code;
    _quit=false;
    _leaf=0;
    ASS_EQ(reinterpret_cast<size_t>(_addr)%8,0);
    while(!_quit) {
      ASS_GE((void*)_addr,(void*)_code);
      ASS_L((void*)_addr,(void*)_afterLastCode);
      ASS_EQ(reinterpret_cast<size_t>(_addr)%8,0);
      typedef void (*OpHandler)(CompiledTree*);
      OpHandler hndl=fromSizeT<OpHandler>(readLong(_addr));
      (*hndl)(this);
//      switch(readLong(_addr)) {
//      case OP_MATCH_TERM:
//	opMatchTerm(this);
//	break;
//      case OP_MATCH_GROUND_TERM:
//	opMatchGroundTerm(this);
//	break;
//      case OP_MATCH_NEW_VAR:
//	opMatchNewVar(this);
//	break;
//      case OP_MATCH_ENCOUNTERED_VAR:
//	opMatchEncounteredVar(this);
//	break;
//      case OP_SKIP_IRRELEVANT_CHILDREN:
//	opSkipIrrelevantChildren(this);
//	break;
//      case OP_LEAF:
//	opLeaf(this);
//	break;
//      case OP_FAIL:
//	opFail(this);
//#if VDEBUG
//	break;
//      default:
//	ASSERTION_VIOLATION;
//#endif
//      }
    }
  }

  static void opMatchNewVar(CompiledTree* ct)
  {
    TermList* qTerm=static_cast<TermList*>(readPtr(ct->_addr));
    unsigned var=static_cast<unsigned>(readLong(ct->_addr));
    if(var>ct->_maxVar) {
      ct->_addr=getAddr(ct->_addr);
    } else {
      ct->_ovBindings[var]=*qTerm;
      shiftByLong(ct->_addr);
    }
  }

  static void opMatchEncounteredVar(CompiledTree* ct)
  {
    TermList* qTerm=static_cast<TermList*>(readPtr(ct->_addr));
    unsigned var=static_cast<unsigned>(readLong(ct->_addr));
    if(var>ct->_maxVar || ct->_ovBindings[var]!=*qTerm) {
      ct->_addr=getAddr(ct->_addr);
    } else {
      shiftByLong(ct->_addr);
    }
  }
  static void opMatchTerm(CompiledTree* ct)
  {
    ct->_nextSpecVarPtr=static_cast<TermList*>(readPtr(ct->_addr));
    TermList* qTerm=static_cast<TermList*>(readPtr(ct->_addr));
    TermList nTerm(readLong(ct->_addr));
    ASS(qTerm->isTerm());
    ASS(nTerm.isTerm());
    ASS_EQ(nTerm.term()->functor(),qTerm->term()->functor());
    if(!MatchingUtils::matchArgs(nTerm.term(),qTerm->term(),*ct)) {
      ct->_addr=getAddr(ct->_addr);
    } else {
      shiftByLong(ct->_addr);
    }
  }
  static void opMatchGroundTerm(CompiledTree* ct)
  {
    TermList* qTerm=static_cast<TermList*>(readPtr(ct->_addr));
    TermList nTerm(readLong(ct->_addr));
    ASS(qTerm->isTerm());
    ASS(nTerm.isTerm());
    ASS_EQ(nTerm.term()->functor(),qTerm->term()->functor());
    if(nTerm!=*qTerm) {
      ct->_addr=getAddr(ct->_addr);
    } else {
      shiftByLong(ct->_addr);
    }
  }
  static void opLeaf(CompiledTree* ct)
  {
    ct->_leaf=static_cast<Leaf*>(readPtr(ct->_addr));
    ASS(ct->_leaf->isLeaf());
    ct->_quit=true;
  }
  static void opFail(CompiledTree* ct)
  {
    ct->_quit=true;
  }
  static void opSkipIrrelevantChildren(CompiledTree* ct)
  {
    TermList* queryTerm=static_cast<TermList*>(readPtr(ct->_addr));
    char* failPnt=readAddr(ct->_addr);
    if(queryTerm->isVar()) {
      ct->_addr=failPnt;
      return;
    }

    size_t termChildCnt=ct->readLong(ct->_addr);
    ASS_LE(termChildCnt, env.signature->functions());
    if(queryTerm->isTerm()) {
      unsigned queryFunctor=queryTerm->term()->functor();
      int min_i=0;
      int max_i=static_cast<int>(termChildCnt-1);
      while(min_i<=max_i) {
	int i=(min_i+max_i)/2;
        size_t nodeFunctor=getLong(ct->_addr+i*2*sizeof(void*));
        if(nodeFunctor>queryFunctor) {
          max_i=i-1;
        } else if(nodeFunctor<queryFunctor) {
          min_i=i+1;
        } else {
          ct->_addr=getAddr(ct->_addr+(i*2+1)*sizeof(void*));
          return;
        }
      }
    }
    ct->_addr=failPnt;
  }

  /**
   * Ensure variable @b var is bound to @b term. Return false iff
   * it is not possible. If a new binding was creater, push @b var
   * onto parent's @b _boundVars stack.
   */
  bool bind(unsigned var, TermList term)
  {
    bool first=var&NEW_VARIABLE_MARK;
    var=var&~NEW_VARIABLE_MARK;
    if(var > _maxVar) {
      return false;
    }
    if( first ) {
      _ovBindings[var]=term;
      return true;
    } else {
      return _ovBindings[var]==term;
    }
  }
  /**
   * Bind special variable @b var to @b term, and push @b var
   * onto @b _newSpecVars stack.
   */
  inline
  void specVar(unsigned var, TermList term)
  {
    ASS_L(_nextSpecVarPtr, _afterLastAllocatedSVBinding);
    *(_nextSpecVarPtr++)=term;
//    _svBindings[var]=term;
  }

  char* _addr;
  Leaf* _leaf;
  bool _quit;
  TermList* _nextSpecVarPtr;

  unsigned _maxVar;
  unsigned _ovBindingsSize;
  TermList* _ovBindings;
  TermList* _svBindings;
  SubstitutionTree* _parent;
  char* _code;

  size_t OP_MATCH_TERM;
  size_t OP_MATCH_GROUND_TERM;
  size_t OP_MATCH_NEW_VAR;
  size_t OP_MATCH_ENCOUNTERED_VAR;
  size_t OP_SKIP_IRRELEVANT_CHILDREN;
  size_t OP_LEAF;
  size_t OP_FAIL;

//  static const size_t OP_MATCH_TERM=1;
//  static const size_t OP_MATCH_GROUND_TERM=2;
//  static const size_t OP_MATCH_NEW_VAR=3;
//  static const size_t OP_MATCH_ENCOUNTERED_VAR=4;
//  static const size_t OP_SKIP_IRRELEVANT_CHILDREN=5;
//  static const size_t OP_LEAF=6;
//  static const size_t OP_FAIL=7;

#if VDEBUG
  char* _afterLastCode;
  char* _afterLastAllocatedCode;
  TermList* _afterLastAllocatedSVBinding;
#endif
};


SubstitutionTree::CompiledTree* SubstitutionTree::compiledTreeCreate(SubstitutionTree *parent,
	IntermediateNode* root, unsigned initBindingCount)
{
  env.timer->stop();
  CompiledTree* res=new CompiledTree(parent, root, initBindingCount);
  env.timer->start();
  return res;
}
void SubstitutionTree::compiledTreeDestroy(CompiledTree* ct)
{
  delete ct;
}

void SubstitutionTree::compiledTreeInitForRetrieval(CompiledTree* ct, Term* query)
{
  ct->initForRetrieval(query);
}

void SubstitutionTree::compiledTreeInitSpecVar(CompiledTree* ct, unsigned var, TermList term)
{
  ct->_svBindings[var]=term;
}
SubstitutionTree::Leaf* SubstitutionTree::compiledTreeGetNextLeaf(CompiledTree* ct)
{
  return ct->getNextLeaf();
}


}

