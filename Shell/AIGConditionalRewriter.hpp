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
private:

  struct QuantInfo {
    QuantInfo(unsigned var, bool univ) : var(var), univ(univ) {}

    static bool compareVars(QuantInfo qi1, QuantInfo qi2) { return qi1.var < qi2.var; }

    unsigned var;
    bool univ;
  };

  /** Contains collected quantifiers, the top-most are at the bottom of the stack.
   * Sequences of variables of the same kind are sorted by the variable number */
  typedef Stack<QuantInfo> QIStack;

  void sortQuantSegments(QIStack& qs);
  void collectQuants(AIGRef a, QIStack& quants, AIGRef& inner);
  void unifyQuants(AIGRef a1, const QIStack& q1, AIGRef a2, const QIStack& q2,
      AIGRef& a1res, AIGRef& a2res, QIStack& qres);
  AIGRef processConjunction(AIGRef a);

  AIGInsideOutPosIterator _buildingIterator;
  DHMap<AIGRef,AIGRef> _transfCache;

  AIG& _aig;
  AIGTransformer _atr;
};

class AIGConditionalRewriter {

};

}

#endif // __AIGConditionalRewriter__
