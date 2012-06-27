/**
 * @file AIGConditionalRewriter.hpp
 * Defines class AIGConditionalRewriter.
 */

#ifndef __AIGConditionalRewriter__
#define __AIGConditionalRewriter__

#include "Forwards.hpp"

#include "Lib/FreshnessGuard.hpp"
#include "Lib/ScopedPtr.hpp"

#include "AIG.hpp"
#include "AIGInferenceEngine.hpp"

#define OLD_PRENEX 0

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
  static AIGRef getInner(AIGRef a);
  static bool isPrenex(AIGRef a);


  struct QuantInfo {
    QuantInfo() : var(UINT_MAX) {}
    QuantInfo(unsigned var, bool univ) : var(var), univ(univ) {}

    bool isValid() const { return var!=UINT_MAX; }

    static bool compareVars(QuantInfo qi1, QuantInfo qi2) { return qi1.var < qi2.var; }
    static unsigned getVar(QuantInfo qi) { return qi.var; }

    unsigned var;
    bool univ;
  };

  /** Contains collected quantifiers, the top-most are at the bottom of the stack.
   * Sequences of variables of the same kind are sorted by the variable number */
  typedef Stack<QuantInfo> QIStack;
  /**
   * Quantified AIG, first being the inner AIG and QIStack the quantifiers
   */
  typedef pair<AIGRef,QIStack> QuantAIG;

  static void swapPolarity(QIStack& quants);

  static void collectQuants(AIGRef a, QIStack& quants, AIGRef& inner);
  AIGRef quantifyBySpec(const QIStack& qs, AIGRef inner);

private:
  static void sortQuantSegments(QIStack& qs);


#if OLD_PRENEX
  struct QuantUnifier;

  void unifyQuants(AIG::VarSet* freeVars, AIGRef a1, const QIStack& q1, AIGRef a2, const QIStack& q2,
      AIGRef& a1res, AIGRef& a2res, QIStack& qres);
  AIGRef processConjunction(AIGRef a);

  AIGInsideOutPosIterator _buildingIterator;
  DHMap<AIGRef,AIGRef> _transfCache;
#else
  struct QuantUnifierN;
  struct RecursiveVisitor;
#endif

  unsigned getVarSort(AIGRef a, unsigned var);

  AIG& _aig;
  AIGTransformer _atr;

  typedef pair<AIGRef,unsigned> VarSortCacheKey;
  /** Map from (positive aig,variable number) to sort number */
  DHMap<VarSortCacheKey,unsigned> _varSorts;
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

class AIGConditionalRewriter
{
public:

  AIGConditionalRewriter();

  void apply(Problem& prb);
  void apply(UnitList*& units);
  AIGRef apply(AIGRef a);


private:

  AIGRef applyInner(AIGRef a);

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

    AIGRef getDisjunctiveRepr(AIG& aig)
    {
      CALL("AIGConditionalRewriter::Equiv::getDisjunctiveRepr");
      return aig.getDisj(aig.getConj(first, second), aig.getConj(first.neg(), second.neg()));
    }

    AIGRef first;
    AIGRef second;
  };

  typedef Stack<AIGRef> AIGStack;
  typedef Stack<Equiv> EquivStack;

  AIGRef getOppositeImpl(AIGRef a);
  bool isDisjEquiv(AIGRef a, Equiv& eq);



  void collectConjEquivs(AIGStack& conjStack, EquivStack& res);
  void collectEquivs(AIGStack& conjStack, EquivStack& res);


  AIGPrenexTransformer::QIStack _prenexQuantifiers;

  //object can be used only once
  FreshnessGuard _freshnessGuard;

  ScopedPtr<AIGInferenceEngine> _engine;

  AIGFormulaSharer _afs;
  AIG& _aig;
};

}

#endif // __AIGConditionalRewriter__
