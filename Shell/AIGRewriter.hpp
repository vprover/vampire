/**
 * @file AIGRewriter.hpp
 * Defines class AIGRewriter.
 */

#ifndef __AIGRewriter__
#define __AIGRewriter__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"

#include "AIG.hpp"

namespace Shell {

using namespace Lib;

class AIGRewriter {
  struct L0DerefQueryRec;

  AIG& _aig;

  DHMap<unsigned, Unit*> _premMap;
public:
  unsigned getPremiseNum(Unit* u);
  Unit* getPremiseUnit(unsigned u);

  typedef const SharedSet<unsigned> PremiseSet;
  typedef AIGRef Ref;

  typedef Stack<PremiseSet*> PremSetStack;

  typedef pair<Ref,PremiseSet*> PremRef;

  /**
   * Map specifying a rewrite for references. A requirement is
   * that the map domain consists only of references with positive
   * polarity and that it is acyclic. Then it can be saturated to
   * become a congruence on the AIG.
   */
  typedef DHMap<Ref,PremRef> RefMap;

  static Ref lev0Deref(Ref r, RefMap& map, PremiseSet** prem);
  Ref lev1Deref(Ref r, RefMap& map, PremiseSet** premAcc);
private:

  typedef MapToLIFO<Ref,Ref> RefEdgeMap;
//
//  void addAIGPredecessors(AIGStack& stack);
//  void orderTopologically(AIGStack& stack);
  void collectUsed(Ref r, const RefMap& map, RefEdgeMap& edges);
//
  void saturateOnTopSortedStack(const AIGStack& stack, RefMap& map);

public:
  AIGRewriter(AIG& aig) : _aig(aig) {}

//  void makeOrderedAIGGraphStack(AIGStack& stack);
  void restrictToGetOrderedDomain(RefMap& map, AIGStack& domainOrder);
  void saturateMap(RefMap& map, Stack<Ref>* finalDomain=0);

  void applyWithCaching(Ref r, RefMap& map);
  void makeIdempotent(RefMap& map, Stack<Ref>* finalDomain=0);

};

}

#endif // __AIGRewriter__
