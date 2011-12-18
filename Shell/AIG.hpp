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

#include "Kernel/Formula.hpp"
#include "Kernel/FormulaTransformer.hpp"



namespace Shell {

using namespace Lib;
using namespace Kernel;

class AIGTransformer;

class AIG {
public:
  friend class AIGTransformer;

  class Node;
  typedef Formula::VarList VarList;

  class Ref {
    friend class AIG;
    friend class AIGTransformer;
    size_t _data;

    Ref(Node* n, bool polarity) {
      CALL("AIG::Ref::Ref");
      ASS_EQ(reinterpret_cast<size_t>(n)&1,0); //check pointer alignment

      _data = reinterpret_cast<size_t>(n) | polarity;
    }
    Node* node() const { return reinterpret_cast<Node*>(_data&(~static_cast<size_t>(1))); }
  public:
    Ref() {}
    bool isPropConst() const;
    bool isTrue() const { return isPropConst() && polarity(); }
    bool isFalse() const  { return isPropConst() && !polarity(); }
    Ref neg() const { return Ref(node(), !polarity()); }
    bool polarity() const { return _data&1; }

    bool operator==(const Ref& r) const { return _data==r._data; }
    bool operator!=(const Ref& r) const { return !((*this)==r); }

    bool operator<(const Ref& r) const;
    bool operator>(const Ref& r) const { return r<(*this); }
    bool operator>=(const Ref& r) const { return !((*this)<r); }
    bool operator<=(const Ref& r) const { return !(r<(*this)); }

    unsigned hash() const;
    string toString() const;
  };
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
  Node* univQuantNode(VarList* vars, Ref par);

  void normalizeRefOrder(Ref& par1, Ref& par2);

  //simplifications according to
  //Brummayer, R., Biere, A.: Local Two-Level And-Inverter Graph Minimization without Blowup
  bool tryO1ConjSimpl(Ref par1, Ref par2, Ref& res);
  bool tryO2ConjSimpl(Ref par1, Ref par2, Ref& res);
  bool tryO2AsymetricConjSimpl(Ref par1, Ref par2, Ref& res);
  bool tryO3ConjSimpl(Ref& par1, Ref& par2);
  bool tryO3AsymetricConjSimpl(Ref& par1, Ref& par2);
  bool tryO4ConjSimpl(Ref& par1, Ref& par2);
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
  Ref getQuant(bool exQuant, VarList* vars, Ref par);
};

typedef AIG::Ref AIGRef;

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
  typedef Stack<Ref> RefStack;
private:
  typedef MapToLIFO<Ref,Ref> RefEdgeMap;

  Ref lev0Deref(Ref r, RefMap& map);
  Ref lev1Deref(Ref r, RefMap& map);

  void addPredecessors(RefStack& stack, const RefMap& map);
  void orderTopologically(RefStack& stack);
  void collectUsed(Ref r, const RefMap& map, RefEdgeMap& edges);

  void saturateOnTopSortedStack(const RefStack& stack, RefMap& map);
  void applyWithCaching(Ref r, RefMap& map);

  void makeIdempotent(RefMap& map);
public:
  AIGTransformer(AIG& aig) : _aig(aig) {}

  void saturateMap(RefMap& map);
};

class AIGFormulaSharer
{
public:
  typedef pair<Formula*,AIGRef> ARes;
private:
  AIG _aig;

  DHMap<AIGRef,Formula*> _formReprs;



  Formula* shareFormula(Formula* f, AIGRef aig);


  ARes applyTrueFalse(Formula* f);
  ARes applyLiteral(Formula* f);
  ARes applyJunction(Formula* f);
  ARes applyNot(Formula* f);
  ARes applyBinary(Formula* f);
  ARes applyQuantified(Formula* f);

public:
  ARes apply(Formula * f);

  void apply(Problem& prb);
  bool apply(UnitList*& units);
  bool apply(FormulaUnit* unit, FormulaUnit*& res);
};


#if 0
class AIGDefinitionMerger {
public:
  void apply(Problem& prb);
  bool apply(UnitList*& units);

  void discoverEquivalences(UnitList* units, UnitList*& eqs, DHSet<Unit*>& redundant);
};
#endif
}

#endif // __AIG__
