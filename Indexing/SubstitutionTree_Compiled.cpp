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

class SubstitutionTree::CompiledTree
{
public:
  CompiledTree(SubstitutionTree *parent, IntermediateNode* root)
  : _ovBindings(0)
  {
    CALL("SubstitutionTree::CompiledTree::CompiledTree");

    _svBindings=static_cast<TermList*>(
	    ALLOC_UNKNOWN(parent->_nextVar*sizeof(size_t), "SubstitutionTree::CompiledTree::_svBindings"));
    size_t maxTreeSize=getMaxTreeSize(root);
    _code=static_cast<char*>(
	    ALLOC_UNKNOWN(maxTreeSize, "SubstitutionTree::CompiledTree::_code"));
#if VDEBUG
    _afterLastAllocatedCode=_code+maxTreeSize;
#endif
//    env.timer->stop();
    compileTree(root);
//    env.timer->start();
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
	      ALLOC_UNKNOWN(_ovBindingsSize*sizeof(Node*),"SubstitutionTree::CompiledTree::_ovBindings"));
    }
    _maxVar=query->weight();
  }

  Leaf* getNextLeaf()
  {
    run();
    return _leaf;
  }

  static const size_t OP_MATCH_TERM=1;
  static const size_t OP_MATCH_NEW_VAR=2;
  static const size_t OP_MATCH_ENCOUNTERED_VAR=3;
  static const size_t OP_LEAF=4;
  static const size_t OP_FAIL=5;
  static size_t getMaxOpSize(Node* n)
  {
    if(n->isLeaf()) {
      return 48;
    } else {
      return 32;
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

  char* storeNode(char*& addr, Node* node, unsigned specVar)
  {
    TermList nodeTerm=node->term;
    if(nodeTerm.isVar()) {
      bool marked=nodeTerm.var()&NEW_VARIABLE_MARK;
      if(marked) {
	storeLong(addr, OP_MATCH_NEW_VAR);
      } else {
	storeLong(addr, OP_MATCH_ENCOUNTERED_VAR);
      }
      storePtr(addr, &_svBindings[specVar]);
      storeLong(addr, nodeTerm.var()&~NEW_VARIABLE_MARK);
    } else {
      storeLong(addr, OP_MATCH_TERM);
      storePtr(addr, &_svBindings[specVar]);
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

  void compileTree(IntermediateNode* root)
  {
    CALL("SubstitutionTree::CompiledTree::compileTree");

    static Stack<Node*> nexts(32);
    static Stack<NodeIterator> alts(32);
    static Stack<unsigned> specVars(32);
    nexts.reset();
    alts.reset();
    specVars.reset();

    FailPointTargetStore failPointTargets;
    ASS(root->term.isEmpty());

    char* addr=_code;

    nexts.push(0);
    specVars.push(root->childVar);

    alts.push(root->allChildren());
    ASS(alts.top().hasNext());
    nexts.push(*alts.top().next());

    for(;;) {
      if(alts.isEmpty()) {
	break;
      }
      Node* curr=nexts.pop();
      unsigned specVar=specVars.top();
      if(alts.top().hasNext()) {
	nexts.push(*alts.top().next());
      } else {
	alts.pop();
	specVars.pop();
      }
      //fill in address of this node, where it's needed as a fail point
      fillInFailPoints(failPointTargets, curr, addr);

      char* prevAddr=addr;
      char* failPntTgt=storeNode(addr,curr,specVar);
      ASS_REP((addr-prevAddr)==8*4 || (addr-prevAddr)==8*6, addr-prevAddr);

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
      ASS_L(_addr,_afterLastCode);
      switch(readLong(_addr)) {
      case OP_MATCH_TERM:
	opMatchTerm();
	break;
      case OP_MATCH_NEW_VAR:
	opMatchNewVar();
	break;
      case OP_MATCH_ENCOUNTERED_VAR:
	opMatchEncounteredVar();
	break;
      case OP_LEAF:
	opLeaf();
	break;
      case OP_FAIL:
	opFail();
#if VDEBUG
	break;
      default:
	ASSERTION_VIOLATION;
#endif
      }
    }
  }

  void opMatchNewVar()
  {
    TermList* qTerm=static_cast<TermList*>(readPtr(_addr));
    unsigned var=static_cast<unsigned>(readLong(_addr));
    if(var>_maxVar) {
      _addr=readAddr(_addr);
    } else {
      _ovBindings[var]=*qTerm;
      shiftByLong(_addr);
    }
  }

  void opMatchEncounteredVar()
  {
    TermList* qTerm=static_cast<TermList*>(readPtr(_addr));
    unsigned var=static_cast<unsigned>(readLong(_addr));
    if(var>_maxVar || _ovBindings[var]!=*qTerm) {
      _addr=readAddr(_addr);
    } else {
      shiftByLong(_addr);
    }
  }
  void opMatchTerm()
  {
    TermList* qTerm=static_cast<TermList*>(readPtr(_addr));
    TermList nTerm(readLong(_addr));
    if(!MatchingUtils::matchTerms(nTerm,*qTerm,*this)) {
      _addr=readAddr(_addr);
    } else {
      shiftByLong(_addr);
    }
  }
  void opLeaf()
  {
    _leaf=static_cast<Leaf*>(readPtr(_addr));
    ASS(_leaf->isLeaf());
    _quit=true;
  }
  void opFail()
  {
    _quit=true;
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
    _svBindings[var]=term;
  }

  char* _addr;
  Leaf* _leaf;
  bool _quit;

  unsigned _maxVar;
  unsigned _ovBindingsSize;
  TermList* _ovBindings;
  TermList* _svBindings;
  SubstitutionTree* _parent;
  char* _code;

#if VDEBUG
  char* _afterLastCode;
  char* _afterLastAllocatedCode;
#endif
};


SubstitutionTree::CompiledTree* SubstitutionTree::compiledTreeCreate(SubstitutionTree *parent,
	IntermediateNode* root)
{
  return new CompiledTree(parent, root);
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
