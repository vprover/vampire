/**
 * @file AIGConditionalRewriter.hpp
 * Defines class AIGConditionalRewriter.
 */

#ifndef __AIGConditionalRewriter__
#define __AIGConditionalRewriter__

#include "Forwards.hpp"

#include "AIG.hpp"

namespace Shell {

/**
 * Converts AIGs into prenex form
 */
class AIGPrenexTransformer
{
public:
  AIGPrenexTransformer(AIG& aig) : _aig(aig), _atr(aig) {}

  AIGRef apply(AIGRef a);
  static bool containsQuant(AIGRef a);
  static bool isPrenex(AIGRef a);


  struct QuantInfo {
    QuantInfo() : var(UINT_MAX) {}
    QuantInfo(unsigned var, bool univ) : var(var), univ(univ) {}

    bool isValid() const { return var!=UINT_MAX; }

    static bool compareVars(QuantInfo qi1, QuantInfo qi2) { return qi1.var < qi2.var; }

    unsigned var;
    bool univ;
  };

  /** Contains collected quantifiers, the top-most are at the bottom of the stack.
   * Sequences of variables of the same kind are sorted by the variable number */
  typedef Stack<QuantInfo> QIStack;

  void collectQuants(AIGRef a, QIStack& quants, AIGRef& inner);
  AIGRef quantifyBySpec(const QIStack& qs, AIGRef inner);

private:



  struct QuantUnifier;

  static void sortQuantSegments(QIStack& qs);
  void unifyQuants(AIG::VarSet* freeVars, AIGRef a1, const QIStack& q1, AIGRef a2, const QIStack& q2,
      AIGRef& a1res, AIGRef& a2res, QIStack& qres);
  AIGRef processConjunction(AIGRef a);

  AIGInsideOutPosIterator _buildingIterator;
  DHMap<AIGRef,AIGRef> _transfCache;

  AIG& _aig;
  AIGTransformer _atr;
};

class AIGMiniscopingTransformer
{
public:
  AIGMiniscopingTransformer(AIG& aig) : _aig(aig), _atr(aig) {}

  AIGRef apply(AIGRef a0);
private:

  AIGRef processQuantifier(AIGRef a);

  AIGInsideOutPosIterator _buildingIterator;
  DHMap<AIGRef,AIGRef> _transfCache;

  AIG& _aig;
  AIGTransformer _atr;
};

class AIGFactorizingTransformer
{
public:
  AIGFactorizingTransformer(AIG& aig) : _aig(aig), _atr(aig) {}

  AIGRef apply(AIGRef a0);
private:
  typedef AIGTransformer::RefMap RefMap;
  struct RecursiveVisitor;
  struct LocalFactorizer;

  void doLocalFactorization(AIGStack& conj);

  RefMap _transfCache;

  AIG& _aig;
  AIGTransformer _atr;
};

//class AIGInferenceEngine
//{
//public:
//  void addValidNode(AIGRef node);
//  void removeValidNode(AIGRef node);
//
//  AIGRef simplify(AIGRef a, AIGStack* premises);
//};

class AIGConditionalRewriter
{
public:

  AIGConditionalRewriter();

  void apply(Problem& prb);
  void apply(UnitList*& units);
  AIGRef apply(AIGRef a);


private:

  /**
   * Represents normalized implication
   */
  struct Impl {
    Impl() {}
    Impl(AIGRef lhs_, AIGRef rhs_) : lhs(lhs_), rhs(rhs_)
    {
      CALL("AIGConditionalRewriter::Impl::Impl");
      ASS_NEQ(lhs.getPositive(), rhs.getPositive());

      bool shouldSwap = false;
      if(!lhs.polarity() && !rhs.polarity()) {
	shouldSwap = true;
      }
      if(lhs.polarity()!=rhs.polarity()) {
	//we cannot normalize the polarity by swapping, so we normalize the order
	//of aigs
	if(lhs.nodeIndex()>rhs.nodeIndex()) {
	  shouldSwap = true;
	}
      }
      if(shouldSwap) {
	//~a -> ~b  ==>  b -> a
	swap(lhs, rhs);
	lhs = lhs.neg();
	rhs = rhs.neg();
      }
    }
    AIGRef lhs;
    AIGRef rhs;
  };

  /**
   * Represents normalized equivalence
   */
  struct Equiv {
    Equiv() {}
    Equiv(AIGRef first_, AIGRef second_) : first(first_), second(second_)
    {
      CALL("AIGConditionalRewriter::Equiv::Equiv");
      ASS_NEQ(first.getPositive(), second.getPositive());

      if(first.nodeIndex()>second.nodeIndex()) {
	swap(first,second);
      }

      if(!first.polarity()) {
	first = first.neg();
	second = second.neg();
      }
    }

    string toString() const { return "EQ: "+first.toString()+" <=> "+second.toString(); }

    AIGRef first;
    AIGRef second;
  };

  typedef Stack<AIGRef> AIGStack;
  typedef Stack<Equiv> EquivStack;

  AIGRef getOppositeImpl(AIGRef a);
  bool isDisjEquiv(AIGRef a, Equiv& eq);



  void collectConjEquivs(AIGStack& conjStack, EquivStack& res);
  void collectEquivs(AIGStack& conjStack, EquivStack& res);



  AIGFormulaSharer _afs;
  AIG& _aig;
};

}

#endif // __AIGConditionalRewriter__
