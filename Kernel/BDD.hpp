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

/**
 * A class of objects representing nodes in binary decision diagrams.
 */
class BDDNode
{
public:
  CLASS_NAME("BDDNode");
  USE_ALLOCATOR(BDDNode);
private:
  BDDNode() {}
  BDDNode(int var, BDDNode* pos, BDDNode* neg) : _var(var), _pos(pos), _neg(neg) {}

  int _var;
  BDDNode* _pos;
  BDDNode* _neg;

  friend class BDD;
  friend class BDDConjunction;
};

/**
 * A class of binary decision diagrams.
 *
 * The BDD object is a singleton, the instance can be obtained by
 * the @b instance() method.
 */
class BDD
{
public:
  static BDD* instance();

  BDD();
  ~BDD();

  /** Return an unused BDD variable number */
  int getNewVar() { return _newVar++; }
  int getNewVar(unsigned pred);

  string getPropositionalPredicateName(int var);
  bool getNiceName(int var, string& res);
  Signature::Symbol* getSymbol(int var);

  /** Return a BDD node representing true formula */
  BDDNode* getTrue() { return &_trueNode; }
  /** Return a BDD node representing false formula */
  BDDNode* getFalse() { return &_falseNode; }

  BDDNode* getAtomic(int varNum, bool positive);

  BDDNode* conjunction(BDDNode* n1, BDDNode* n2);
  BDDNode* disjunction(BDDNode* n1, BDDNode* n2);
  BDDNode* xOrNonY(BDDNode* x, BDDNode* y);
  /** Return a BDD node of negation of @b n */
  BDDNode* negation(BDDNode* n)
  { return xOrNonY(getFalse(), n); }

  bool isXOrNonYConstant(BDDNode* x, BDDNode* y, bool resValue);

  /** Return @b true iff @b node represents a true formula */
  bool isTrue(BDDNode* node) { return node==getTrue(); }
  /** Return @b true iff @b node represents a false formula */
  bool isFalse(BDDNode* node) { return node==getFalse(); }
  /** Return @b true iff @b node represents either a false or a true formula */
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

  /**
   * A functor used by @b getBinaryFnResult to compute the conjunction of two BDDs,
   * and by @b hasConstantResult to check whether the conjunction of two BDDs is
   * either a true or a false formula.
   */
  struct ConjunctionFn
  {
    ConjunctionFn(BDD* parent) : _parent(parent) {}
    inline BDDNode* operator()(BDDNode* n1, BDDNode* n2);
    BDD* _parent;
  };

  /**
   * A functor used by @b getBinaryFnResult to compute the disjunction of two BDDs,
   * and by @b hasConstantResult to check whether the disjunction of two BDDs is
   * either a true or a false formula.
   */
  struct DisjunctionFn
  {
    DisjunctionFn(BDD* parent) : _parent(parent) {}
    inline BDDNode* operator()(BDDNode* n1, BDDNode* n2);
    BDD* _parent;
  };

  /**
   * A functor used by @b getBinaryFnResult to compute X | ~Y of two BDDs X and Y,
   * and by @b hasConstantResult to check whether X | ~Y of two BDDs X and Y is
   * either a true or a false formula.
   */
  struct XOrNonYFn
  {
    XOrNonYFn(BDD* parent) : _parent(parent) {}
    inline BDDNode* operator()(BDDNode* n1, BDDNode* n2);
    BDD* _parent;
  };


  /** BDD node representing the true formula */
  static BDDNode _trueNode;
  /** BDD node representing the false formula */
  static BDDNode _falseNode;

  /** Type that stores the set of all non-constant BDD nodes */
  typedef Set<BDDNode*,BDD> NodeSet;
  /** The set storing all nodes */
  NodeSet _nodes;

  /**
   * Predicate symbols corresponding to BDD variables
   *
   * Not all BDD variables must have a corresponding predicate.
   */
  DHMap<int, unsigned> _predicateSymbols;


  /** The next unused BDD variable */
  int _newVar;
};

/**
 * A class of objects that keep a conjunction of multiple BDDs.
 *
 * Keeping conjunction of multiple BDDs using this class shows to
 * be more efficient for large BDDs than just using a BDD conjunction
 * operation, as here we use an incremental SAT solver to check whether
 * the conjunction is a satisfiable formula or not.
 */
class BDDConjunction
{
public:
  BDDConjunction() : _isFalse(false), _maxVar(-1) {}
  void addNode(BDDNode* n);

  /** Return @b true iff the conjunction represented by this object is unsatisfiable */
  bool isFalse() { return _isFalse; }
private:
  /** Is equal to @b true iff the conjunction represented by this object is unsatisfiable */
  bool _isFalse;
  /** Maximal BDD variable that appears in this object */
  int _maxVar;

  /**
   * Two-watched-literal incremental SAT solver that is used to check whether
   * the conjunction represented by this object is satisfiable
   */
  TWLSolver _solver;
};

};

#endif /* __BDD__ */
