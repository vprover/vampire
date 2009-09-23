/**
 * @file BDD.hpp
 * Defines classes BDD and BDDNode for binary decision diagrams
 */

#ifndef __BDD__
#define __BDD__

#include <iosfwd>
#include <string>

#include "../Forwards.hpp"
#include "../Lib/Allocator.hpp"
#include "../Lib/Array.hpp"
#include "../Lib/DHMap.hpp"
#include "../Lib/Hash.hpp"
#include "../Lib/Int.hpp"
#include "../Lib/List.hpp"
#include "../Lib/Set.hpp"
#include "../Lib/SkipList.hpp"
#include "../Lib/Stack.hpp"

#include "../Kernel/Signature.hpp"

#include "../SAT/TWLSolver.hpp"

#define BDD_PREDICATE_PREFIX "$bdd"

namespace Kernel {

using namespace std;
using namespace Lib;
using namespace SAT;

class BDDConjunction;

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
  friend class BDDConjunction;
};

class BDD
{
public:
  static BDD* instance();

  BDD();
  ~BDD();

  int getNewVar() { return _newVar++; }
  int getNewVar(unsigned pred);

  string getPropositionalPredicateName(int var);
  bool getNiceName(int var, string& res);
  Signature::Symbol* getSymbol(int var);

  BDDNode* getTrue() { return &_trueNode; }
  BDDNode* getFalse() { return &_falseNode; }

  BDDNode* getAtomic(int varNum, bool positive);

  BDDNode* conjunction(BDDNode* n1, BDDNode* n2);
  BDDNode* disjunction(BDDNode* n1, BDDNode* n2);
  BDDNode* xOrNonY(BDDNode* x, BDDNode* y);
  BDDNode* negation(BDDNode* n)
  { return xOrNonY(getFalse(), n); }

  bool isXOrNonYConstant(BDDNode* x, BDDNode* y, bool resValue);

  bool isTrue(BDDNode* node) { return node==getTrue(); }
  bool isFalse(BDDNode* node) { return node==getFalse(); }
  bool isConstant(BDDNode* node) { return node->_var==-1; }

  static bool equals(const BDDNode* n1,const BDDNode* n2);
  static unsigned hash(const BDDNode* n);

  string toString(BDDNode* node);
  string toTPTPString(BDDNode* node, string bddPrefix);
  string toTPTPString(BDDNode* node);

  SATClauseList* toCNF(BDDNode* node);

private:
  BDDNode* getNode(int varNum, BDDNode* pos, BDDNode* neg);

  template<class BinBoolFn>
  BDDNode* getBinaryFnResult(BDDNode* n1, BDDNode* n2, BinBoolFn fn);

  template<class BinBoolFn>
  bool hasConstantResult(BDDNode* n1, BDDNode* n2, bool resValue, BinBoolFn fn);

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

  /**
   * Predicate symbols corresponding to BDD variables
   *
   * Not all BDD variables must have a corresponding predicate.
   */
  DHMap<int, unsigned> _predicateSymbols;


  int _newVar;
};

class BDDConjunction
{
public:
  BDDConjunction() : _bdd(BDD::instance()), _isFalse(false), _maxVar(-1), _clauses(0) {}
  void addNode(BDDNode* n);
  bool isFalse() { return _isFalse; }
private:
  BDD* _bdd;
  bool _isFalse;
  int _maxVar;

  SATClauseList* _clauses;
  SATClauseList* _units;

  TWLSolver _solver;
};

};

#endif /* __BDD__ */
