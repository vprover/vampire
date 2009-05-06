/**
 * @file BDD.hpp
 * Defines classes BDD and BDDNode for binary decision diagrams
 */

#ifndef __BDD__
#define __BDD__

#include <iosfwd>

#include "../Forwards.hpp"
#include "../Lib/Allocator.hpp"
#include "../Lib/Hash.hpp"
#include "../Lib/Set.hpp"


namespace Kernel {

class BDDNode
{
public:
  CLASS_NAME("BDDNode");
  USE_ALLOCATOR(BDDNode);
private:
  BDDNode() {}

  int _var;
  BDDNode* _pos;
  BDDNode* _neg;

  friend class BDD;
};

class BDD
{
public:
  static BDD* instance();

  BDD();
  ~BDD();

  int getNewVar() { return _newVar++; }

  BDDNode* getTrue() { return &_trueNode; }
  BDDNode* getFalse() { return &_falseNode; }

  BDDNode* getAtomic(int varNum, bool positive);

  BDDNode* conjunction(BDDNode* n1, BDDNode* n2);
  BDDNode* disjunction(BDDNode* n1, BDDNode* n2);
  BDDNode* xOrNonY(BDDNode* x, BDDNode* y);
  BDDNode* negation(BDDNode* n)
  { return xOrNonY(getFalse(), n); }

  bool isTrue(BDDNode* node) { return node==getTrue(); }
  bool isFalse(BDDNode* node) { return node==getFalse(); }

  static bool equals(const BDDNode* n1,const BDDNode* n2);
  static unsigned hash(const BDDNode* n);

private:
  BDDNode* getNode(int varNum, BDDNode* pos, BDDNode* neg);

  template<class BinBoolFn>
  BDDNode* getBinaryFnResult(BDDNode* n1, BDDNode* n2, BinBoolFn fn);

  struct ConjunctionFn
  {
    ConjunctionFn(BDD* parent) : _parent(parent) {}
    BDDNode* operator()(BDDNode* n1, BDDNode* n2);
    BDD* _parent;
  };

  struct DisjunctionFn
  {
    DisjunctionFn(BDD* parent) : _parent(parent) {}
    BDDNode* operator()(BDDNode* n1, BDDNode* n2);
    BDD* _parent;
  };

  struct XOrNonYFn
  {
    XOrNonYFn(BDD* parent) : _parent(parent) {}
    BDDNode* operator()(BDDNode* n1, BDDNode* n2);
    BDD* _parent;
  };


  BDDNode _trueNode;
  BDDNode _falseNode;

  typedef Set<BDDNode*,BDD> NodeSet;
  /** The set storing all nodes */
  NodeSet _nodes;

  int _newVar;
};

};

#endif /* __BDD__ */
