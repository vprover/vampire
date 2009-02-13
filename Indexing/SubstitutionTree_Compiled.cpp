/**
 * @file SubstitutionTree_Compiled.cpp
 * Implements class SubstitutionTree::CompiledTree.
 */

#include "SubstitutionTree.hpp"

#include "../Lib/Environment.hpp"
#include "../Lib/Timer.hpp"

namespace Indexing {

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
  CompiledTree(SubstitutionTree *parent, IntermediateNode* root, unsigned initBindingCount)
  : _ovBindingsSize(0), _ovBindings(0)
  {
    CALL("SubstitutionTree::CompiledTree::CompiledTree");

    _svBindings=static_cast<TermList*>(
	    ALLOC_UNKNOWN(parent->_nextVar*sizeof(TermList), "SubstitutionTree::CompiledTree::_svBindings"));
    size_t maxTreeSize=getMaxTreeSize(root);
    _code=static_cast<char*>(
	    ALLOC_UNKNOWN(maxTreeSize, "SubstitutionTree::CompiledTree::_code"));
#if VDEBUG
    _afterLastAllocatedCode=_code+maxTreeSize;
    _afterLastAllocatedSVBinding=_svBindings+parent->_nextVar;
#endif

//    OP_MATCH_TERM=toSizeT(&CompiledTree::opMatchTerm);
//    OP_MATCH_NEW_VAR=toSizeT(&CompiledTree::opMatchNewVar);
//    OP_MATCH_ENCOUNTERED_VAR=toSizeT(&CompiledTree::opMatchEncounteredVar);
//    OP_LEAF=toSizeT(&CompiledTree::opLeaf);
//    OP_FAIL=toSizeT(&CompiledTree::opFail);

    compileTree(root, initBindingCount);
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

  static size_t getMaxOpSize(Node* n)
  {
    if(n->isLeaf()) {
      return 56;
    } else {
      return 40;
    }
  }
  static size_t getMaxTreeSize(IntermediateNode* root)
  {
    CALL("SubstitutionTree::CompiledTree::getMaxTreeSize");

    static Stack<NodeIterator> alts(32);
    alts.reset();

    size_t sz=32;

    alts.push(root->allChildren());
    for(;;) {
      while(alts.isNonEmpty()&&!alts.top().hasNext()) {
	alts.pop();
      }
      if(alts.isEmpty()) {
	break;
      }
      Node* curr=*alts.top().next();
      ASS(curr);
      ASSERT_VALID(*curr);
      if(!curr->isLeaf()) {
	alts.push(static_cast<IntermediateNode*>(curr)->allChildren());
      }
      sz+=getMaxOpSize(curr);
    }

    return sz;
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
  static size_t readLong(char*& addr)
  {
    size_t res=*reinterpret_cast<size_t*>(addr);
    shiftByLong(addr);
    return res;
  }
  inline
  static void* readPtr(char*& addr)
  {
    void* res=*reinterpret_cast<void**>(addr);
    shiftByLong(addr);
    return res;
  }
  inline
  static char* readAddr(char*& addr)
  {
    char* res=*reinterpret_cast<char**>(addr);
    shiftByLong(addr);
    return res;
  }
  inline
  static void shiftByLong(char*& addr)
  {
    addr+=sizeof(void*);
  }

  char* storeNode(char*& addr, Node* node, unsigned specVarOfs, unsigned specVarCnt)
  {
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
      storeLong(addr, OP_MATCH_TERM);
      storePtr(addr, &_svBindings[specVarCnt]);
      storePtr(addr, &_svBindings[specVarOfs]);
      storeLong(addr, nodeTerm.content());
    }
    char* failAddrPtr=addr;
    shiftByLong(addr);

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

  typedef DHMap<Node*,List<char*>*, PtrIdentityHash > FailPointTargetStore;

  void fillInFailPoints(FailPointTargetStore& tgts, Node* node, char* point)
  {
    CALL("SubstitutionTree::CompiledTree::fillInFailPoints");

    List<char*>* lst;
    if(!tgts.find(node,lst)) {
      return;
    }
    tgts.remove(node);
    while(lst) {
      char* tgt=List<char*>::pop(lst);
      *reinterpret_cast<char**>(tgt)=point;
    }
  }

  void compileTree(IntermediateNode* root, unsigned initBindingCount)
  {
    CALL("SubstitutionTree::CompiledTree::compileTree");

    static Stack<Node*> nexts(32);
    static Stack<NodeIterator> alts(32);
    static Stack<unsigned> specVars(32);
    static Stack<unsigned> nextSpecVarOffsets(32);
    nexts.reset();
    alts.reset();
    specVars.reset();
    nextSpecVarOffsets.reset();

    unsigned nextSpecVarOfs=initBindingCount;
    static DHMap<unsigned, unsigned, IdentityHash<unsigned> > specVarOffsets;
    for(unsigned i=0;i<initBindingCount;i++) {
      specVarOffsets.set(i,i);
    }

    FailPointTargetStore failPointTargets;
    ASS(root->term.isEmpty());

    char* addr=_code;

    nexts.push(0);
    specVars.push(root->childVar);
    nextSpecVarOffsets.push(nextSpecVarOfs);

    alts.push(root->allChildren());
    ASS(alts.top().hasNext());
    nexts.push(*alts.top().next());

    for(;;) {
      if(alts.isEmpty()) {
	break;
      }
      Node* curr=nexts.pop();
      unsigned specVarOfs=specVarOffsets.get(specVars.top());
      nextSpecVarOfs=nextSpecVarOffsets.top();

      if(alts.top().hasNext()) {
	nexts.push(*alts.top().next());
      } else {
	alts.pop();
	specVars.pop();
	nextSpecVarOffsets.pop();
      }
      //fill in address of this node, where it's needed as a fail point
      fillInFailPoints(failPointTargets, curr, addr);

      char* failPntTgt=storeNode(addr,curr,specVarOfs,nextSpecVarOfs);

      if(curr->term.isTerm() && !curr->term.term()->shared()) {
	Term::VariableIterator vit(curr->term.term());
	while(vit.hasNext()) {
	  TermList v=vit.next();
	  if(v.isSpecialVar()) {
	    specVarOffsets.set(v.var(),nextSpecVarOfs++);
	  }
	}
      }
      ASS_L(nextSpecVarOfs,50);


      //register point where fail point for this node should be stored
      List<char*>** pTgtLst;
      failPointTargets.getValuePtr(nexts.top(), pTgtLst, 0);
      List<char*>::push(failPntTgt, *pTgtLst);

      if(!curr->isLeaf()) {
	IntermediateNode* inode=static_cast<IntermediateNode*>(curr);
	alts.push(inode->allChildren());
	ASS(alts.top().hasNext());
	nexts.push(*alts.top().next());
	specVars.push(inode->childVar);
	nextSpecVarOffsets.push(nextSpecVarOfs);
      }
    }
    fillInFailPoints(failPointTargets, 0, addr);
    storeFail(addr);
#if VDEBUG
    ASS_EQ((addr-_code)%8,0);
    ASS_LE(addr,_afterLastAllocatedCode);
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
      ASS_EQ(reinterpret_cast<size_t>(_addr)%8,0);
      ASS_GE(_addr,_code);
      ASS_L(_addr,_afterLastCode);
//      typedef void (*OpHandler)(CompiledTree*);
//      OpHandler hndl=fromSizeT<OpHandler>(readLong(_addr));
//      (*hndl)(this);
      switch(readLong(_addr)) {
      case OP_MATCH_TERM:
	opMatchTerm(this);
	break;
      case OP_MATCH_NEW_VAR:
	opMatchNewVar(this);
	break;
      case OP_MATCH_ENCOUNTERED_VAR:
	opMatchEncounteredVar(this);
	break;
      case OP_LEAF:
	opLeaf(this);
	break;
      case OP_FAIL:
	opFail(this);
#if VDEBUG
	break;
      default:
	ASSERTION_VIOLATION;
#endif
      }
    }
  }

  static void opMatchNewVar(CompiledTree* ct)
  {
    TermList* qTerm=static_cast<TermList*>(readPtr(ct->_addr));
    unsigned var=static_cast<unsigned>(readLong(ct->_addr));
    if(var>ct->_maxVar) {
      ct->_addr=readAddr(ct->_addr);
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
      ct->_addr=readAddr(ct->_addr);
    } else {
      shiftByLong(ct->_addr);
    }
  }
  static void opMatchTerm(CompiledTree* ct)
  {
    ct->_nextSpecVarPtr=static_cast<TermList*>(readPtr(ct->_addr));
    TermList* qTerm=static_cast<TermList*>(readPtr(ct->_addr));
    TermList nTerm(readLong(ct->_addr));
    if(!MatchingUtils::matchTerms(nTerm,*qTerm,*ct)) {
      ct->_addr=readAddr(ct->_addr);
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

//  size_t OP_MATCH_TERM;
//  size_t OP_MATCH_NEW_VAR;
//  size_t OP_MATCH_ENCOUNTERED_VAR;
//  size_t OP_LEAF;
//  size_t OP_FAIL;

  static const size_t OP_MATCH_TERM=1;
  static const size_t OP_MATCH_NEW_VAR=2;
  static const size_t OP_MATCH_ENCOUNTERED_VAR=3;
  static const size_t OP_LEAF=4;
  static const size_t OP_FAIL=5;

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

