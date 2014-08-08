/**
 * @file AIG.hpp
 * Defines class AIG.
 */

#ifndef __AIG__
#define __AIG__

#include "Forwards.hpp"

#include "Debug/Assertion.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/List.hpp"
#include "Lib/Set.hpp"
#include "Lib/SharedSet.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/FormulaTransformer.hpp"

#define DEBUG_AIG_REF_MEMORY 0

namespace Shell {

using namespace Lib;
using namespace Kernel;

class AIGRewriter;
class AIGTransformer;
class AIGFormulaSharer;

class AIG {
public:
  friend class AIGRewriter;
  friend class AIGTransformer;
  friend class AIGFormulaSharer;

  class Node;
  typedef SharedSet<unsigned> VarSet;

  class Ref {
    friend class AIG;
    /**
     * Either a tagged pointer (with 1 lsb bit) to AIG node,
     * or zero to stand for an invalid AIG.
     */
    size_t _data;

    Ref(Node* n, bool polarity) {
      CALL("AIG::Ref::Ref");
      ASS_EQ(reinterpret_cast<size_t>(n)&1,0); //check pointer alignment
#if DEBUG_AIG_REF_MEMORY
      ASS_ALLOC_TYPE(n, "AIG::Node");
#endif

      _data = reinterpret_cast<size_t>(n) | polarity;
    }
  public:
    Ref() {}
    /**
     * Return true if the current Ref is invalid.
     *
     * This and isValid() are the only operations allowed on invalid refs.
     */
    bool isInvalid() const { return _data==0; }
    /**
     * Return true if the current Ref is valid.
     *
     * This and isInvalid() are the only operations allowed on invalid refs.
     */
    bool isValid() const { return _data!=0; }
    bool isPropConst() const;
    bool isTrue() const { return isPropConst() && polarity(); }
    bool isFalse() const  { return isPropConst() && !polarity(); }
    bool isAtom() const;
    bool isQuantifier() const;
    bool isConjunction() const;
    Ref neg() const { return Ref(node(), !polarity()); }

    Ref getPositive() const { return polarity() ? *this : neg(); }

    Literal* getPositiveAtom() const;
    VarSet* getQuantifierVars() const;

    VarSet* getFreeVars() const;
    unsigned getVarSort(unsigned var) const;
    /**
     * Return color of the AIG. The color can be also COLOR_INVALID,
     * in case the AIG mixes colors.
     */
    Color getColor() const;

    bool polarity() const {
      CALL("AIG::Ref::node()");
      ASS(isValid());
      return _data&1;
    }
    Node* node() const {
      CALL("AIG::Ref::node()");
      ASS(isValid());
      Node* res = reinterpret_cast<Node*>(_data&(~static_cast<size_t>(1)));
#if DEBUG_AIG_REF_MEMORY
      ASS_ALLOC_TYPE(res, "AIG::Node");
#endif
      return res;
    }
    unsigned nodeIndex() const;
    unsigned parentCnt() const;
    Ref parent(unsigned idx) const;

    bool operator==(const Ref& r) const { return _data==r._data; }
    bool operator!=(const Ref& r) const { return !((*this)==r); }

    bool operator<(const Ref& r) const;
    bool operator>(const Ref& r) const { return r<(*this); }
    bool operator>=(const Ref& r) const { return !((*this)<r); }
    bool operator<=(const Ref& r) const { return !(r<(*this)); }

    unsigned hash() const;
    vstring toString() const;
    vstring toInternalString(unsigned depth=1) const;

    static Ref getInvalid() {
      Ref res;
      res._data = 0;
      return res;
    }
  };

  typedef Stack<Ref> AIGStack;
private:
  /** Proxy object for Ref which is without constructor so can be used inside a union */
  struct RefProxy {
    size_t _data;

    RefProxy& operator= (Ref r) { _data = r._data; return *this; }
    operator Ref() const { Ref res; res._data = _data; return res; }
  };


  struct NodeHash {
    static unsigned hash(Node* n);
    static bool equals(Node* n1, Node* n2);
  };

  typedef DHMap<Literal*,Node*> AtomNodeMap;
  typedef Set<Node*,NodeHash> NodeSet;

  unsigned _simplLevel;

  /**
   * Index of next node to be created
   *
   * We assign indexes to nodes so we can deterministically normalize
   * node order in conjunction nodes
   */
  unsigned _nextNodeIdx;

  Node* _trueNode;
  AtomNodeMap _atomNodes;
  /** Compund nodes (conjunctions and quantifiers) */
  NodeSet _compNodes;

  /** reserve for the conjNode() */
  Node* _conjReserve;
  /** reserve for the univQuantNode() */
  Node* _quantReserve;

  /**
   * Stack where nodes refer only to nodes earlier in the stack
   */
  Stack<Ref> _orderedNodeRefs;

  Node* atomNode(Literal* positiveLiteral);
  Node* conjNode(Ref par1, Ref par2);
  Node* univQuantNode(VarSet* vars, Ref par);

  void normalizeRefOrder(Ref& par1, Ref& par2);


  //simplifications according to
  //Brummayer, R., Biere, A.: Local Two-Level And-Inverter Graph Minimization without Blowup
  bool tryO1ConjSimpl(Ref par1, Ref par2, Ref& res);
  bool tryO2ConjSimpl(Ref par1, Ref par2, Ref& res);
  bool tryO2AsymetricConjSimpl(Ref par1, Ref par2, Ref& res);
  bool tryO3ConjSimpl(Ref& par1, Ref& par2);
  bool tryO3AsymetricConjSimpl(Ref& par1, Ref& par2);
  bool tryO4ConjSimpl(Ref& par1, Ref& par2);

  Ref getUnivQuant(VarSet* vars, Ref par);
public:
  AIG();
  ~AIG();
  Ref getTrue() const { return Ref(_trueNode, true); };
  Ref getFalse() const { return Ref(_trueNode, false); };
  Ref getLit(Literal* lit);
  Ref getNeg(Ref r) { return r.neg(); }
  Ref getConj(Ref par1, Ref par2);
  Ref getDisj(Ref par1, Ref par2) { return getConj(par1.neg(), par2.neg()).neg(); }
  /** The function takes over the vars list, it must be legal to destroy it at any point */
  Ref getQuant(bool exQuant, Formula::VarList* vars, Ref par);
  Ref getQuant(bool exQuant, VarSet* vars, Ref par);

  Ref getInvalid() const { return Ref::getInvalid(); }

  void collectConjuncts(Ref aig, AIGStack& res);
  void flattenConjuncts(AIGStack& conjuncts);
  Ref makeConjunction(const AIGStack& conjuncts);

  static VarSet* getTermFreeVars(Term* lit);
  static bool hasPositivePolarity(Ref r) { return r.polarity(); }
};

typedef AIG::Ref AIGRef;
typedef AIG::AIGStack AIGStack;

inline
std::ostream& operator<< (ostream& out, const AIGRef& f)
{
  CALL("operator <<(ostream&,const AIGRef&)");
  return out << f.toString();
}


}

namespace Lib {

template<>
struct FirstHashTypeInfo<Shell::AIGRef> {
  typedef FirstHashTypeInfo Type;

  static unsigned hash(Shell::AIGRef r) { return r.hash(); }
};

}

namespace Shell {

/**
 * Iterator that yields positive sub-aigs of aig, inner first,
 * including the (positive form of) passed aig itself (this is
 * yielded as last).
 *
 * Each aig is yielded exactly once.
 *
 * If an AIG is yielded, it's parents (in positive form) must
 * have been yielded before.
 */
class AIGInsideOutPosIterator
{
public:
  AIGInsideOutPosIterator() { reset(); }
  AIGInsideOutPosIterator(AIGRef a) { reset(a); }
  void reset(AIGRef a=AIGRef::getInvalid());
  void addToTraversal(AIGRef a);

  template<class It>
  void addManyToTraversal(It it) {
    CALL("AIGInsideOutPosIterator::addManyToTraversal");
    while(it.hasNext()) {
      addToTraversal(it.next());
    }
  }

  bool hasNext();
  AIGRef next();
private:
  bool _ready;
  DHSet<AIGRef> _seen;
  Stack<AIGRef> _stack;
};

class AIGTransformer
{
  typedef AIG::Node Node;

  AIG& _aig;
public:
  typedef AIGRef Ref;
  /**
   * Map specifying a rewrite for references. A requirement is
   * that the map domain consists only of references with positive
   * polarity and that it is acyclic. Then it can be saturated to
   * become a congruence on the AIG.
   */
  typedef DHMap<Ref,Ref> RefMap;

  static Ref lev0Deref(Ref r, RefMap& map);
  Ref lev1Deref(Ref r, RefMap& map);
private:

  typedef MapToLIFO<Ref,Ref> RefEdgeMap;

  void addAIGPredecessors(AIGStack& stack);
  void orderTopologically(AIGStack& stack);
  void collectUsed(Ref r, const RefMap& map, RefEdgeMap& edges);

  void saturateOnTopSortedStack(const AIGStack& stack, RefMap& map);

public:
  AIGTransformer(AIG& aig) : _aig(aig) {}

  void makeOrderedAIGGraphStack(AIGStack& stack);
  void restrictToGetOrderedDomain(RefMap& map, AIGStack& domainOrder);
  void saturateMap(RefMap& map, Stack<Ref>* finalDomain=0);

  void applyWithCaching(Ref r, RefMap& map);
  void makeIdempotent(RefMap& map, Stack<Ref>* finalDomain=0);
};

class AIGFormulaSharer
{
public:
  typedef pair<Formula*,AIGRef> ARes;
private:
  //options
  /**
   * Mutually apply the rewrites on their rhs, so that we cache
   * the original formulas instead of having to build them in
   * the aigToFormula() function. Caching the original formulas
   * may lead to the result containing connectives as equivalences
   * instead of just conjunctions and disjunctions.
   */
  bool _preBuildRewriteCache;

  AIG _aig;
  AIGTransformer _transf;

  DHMap<AIGRef,Formula*> _formReprs;
  DHMap<Formula*,AIGRef> _formAIGs;

  /** If false, content of _rewrites is ignored */
  bool _useRewrites;
  /**
   *
   * Rewrite targets must be present in _formReprs.
   */
  DHMap<AIGRef,AIGRef> _rewrites;


  Formula* shareFormula(Formula* f, AIGRef aig);

  ARes getSharedFormula(Formula* f);

  //These functions are only always called from apply(Formula*).
  //They return non-shared formulas, the sharing is introduced in
  //the apply(Formula*) function.
  ARes applyTrueFalse(Formula* f);
  ARes applyLiteral(Formula* f);
  ARes applyJunction(Formula* f);
  ARes applyNot(Formula* f);
  ARes applyBinary(Formula* f);
  ARes applyQuantified(Formula* f);
  ARes applyIte(Formula* f);

  void buildQuantAigFormulaRepr(AIGRef aig, Stack<AIGRef>& toBuild);
  bool tryBuildEquivalenceFormulaRepr(AIGRef aig, Stack<AIGRef>& toBuild);
  void buildConjAigFormulaRepr(AIGRef aig, Stack<AIGRef>& toBuild);

public:
  AIGFormulaSharer();

  AIG& aig() { return _aig; }
  AIGTransformer& aigTransf() { return _transf; }


  void addRewriteRules(unsigned cnt, Formula* const * srcs, Formula* const * tgts, Stack<unsigned>* usedIdxAcc=0);

  AIGRef getAIG(Clause* cl);

  AIGRef apply(Literal* l) { return _aig.getLit(l); }
  ARes apply(Formula* f);

  void apply(Problem& prb);
  bool apply(UnitList*& units);
  bool apply(FormulaUnit* unit, FormulaUnit*& res);

  Formula* aigToFormula(AIGRef aig);
};


}

#endif // __AIG__
