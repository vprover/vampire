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

class AIG {
  class Node;
public:
  typedef Formula::VarList VarList;

  class Ref {
    friend class AIG;
    size_t _data;

    Ref(Node* n, bool polarity) {
      CALL("AIG::Ref::Ref");
      ASS_EQ(reinterpret_cast<size_t>(n)&1,0);

      _data = reinterpret_cast<size_t>(n) | polarity;
    }
    Node* node() const { return reinterpret_cast<Node*>(_data&(~static_cast<size_t>(1))); }
    bool polarity() const { return _data&1; }
  public:
    Ref() {}
    bool isPropConst() const;
    bool isTrue() const { return isPropConst() && polarity(); }
    bool isFalse() const  { return isPropConst() && !polarity(); }
    Ref neg() const { return Ref(node(), !polarity()); }

    bool operator==(const Ref& r) const { return _data==r._data; }
    bool operator!=(const Ref& r) const { return !((*this)==r); }

    bool operator<(const Ref& r) const;
    bool operator>(const Ref& r) const { return r<(*this); }
    bool operator>=(const Ref& r) const { return !((*this)<r); }
    bool operator<=(const Ref& r) const { return !(r<(*this)); }

    unsigned hash() const;
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


  Node* atomNode(Literal* positiveLiteral);
  Node* conjNode(Ref par1, Ref par2);
  Node* univQuantNode(VarList* vars, Ref par);

  void normalizeRefOrder(Ref& par1, Ref& par2);

  bool tryConjSimpl(Ref par1, Ref par2, Ref& res);
  bool tryO1ConjSimpl(Ref par1, Ref par2, Ref& res);
  bool tryO2ConjSimpl(Ref par1, Ref par2, Ref& res);
  bool tryO2AsymetricConjSimpl(Ref par1, Ref par2, Ref& res);
  bool tryO3ConjSimpl(Ref par1, Ref par2, Ref& res);
  bool tryO4ConjSimpl(Ref par1, Ref par2, Ref& res);
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

}

namespace Lib {

template<>
struct FirstHashTypeInfo<Shell::AIGRef> {
  typedef FirstHashTypeInfo Type;

  static unsigned hash(Shell::AIGRef r) { return r.hash(); }
};

}

namespace Shell {

class AIGFormulaSharer
{
  AIG _aig;

  DHMap<AIGRef,Formula*> _formReprs;


  typedef pair<Formula*,AIGRef> ARes;

  Formula* shareFormula(Formula* f, AIGRef aig);

  ARes apply(Formula * f);

  ARes applyTrueFalse(Formula* f);
  ARes applyLiteral(Formula* f);
  ARes applyJunction(Formula* f);
  ARes applyNot(Formula* f);
  ARes applyBinary(Formula* f);
  ARes applyQuantified(Formula* f);

public:
  void apply(Problem& prb);
  bool apply(UnitList*& units);
  bool apply(FormulaUnit* unit, FormulaUnit*& res);
};

}

#endif // __AIG__
