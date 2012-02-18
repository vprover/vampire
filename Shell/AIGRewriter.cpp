/**
 * @file AIGRewriter.cpp
 * Implements class AIGRewriter.
 */

#include "Lib/MapToLIFO.hpp"
#include "Lib/SCCAnalyzer.hpp"
#include "Lib/ScopedPtr.hpp"
#include "Lib/SharedSet.hpp"
#include "Lib/Stack.hpp"

#include "AIGRewriter.hpp"



namespace Shell
{

unsigned AIGRewriter::getPremiseNum(Unit* u)
{
  CALL("AIGRewriter::getPremiseNum");

  unsigned res = u->number();
  _premMap.insert(res, u); //it may or may not already be there
  return res;
}

Unit* AIGRewriter::getPremiseUnit(unsigned u)
{
  CALL("AIGRewriter::getPremiseUnit");

  return _premMap.get(u);
}

/**
 * Record documenting a single dereference step
 */
struct AIGRewriter::L0DerefQueryRec {
  Ref aig;
  /** value of resNeg before dereferencing aig */
  bool neg;
  /** premise we used to dereference aig */
  PremiseSet* prems;

  L0DerefQueryRec(Ref aig, bool neg, PremiseSet* prems) : aig(aig), neg(neg), prems(prems) {}
};

/**
 * Iteratively dereference r in map, not looking at its child
 * nodes (hence level 0).
 * Even though only positve references are allowed in the map,
 * this function handles also negative ones.
 */
AIG::Ref AIGRewriter::lev0Deref(Ref r, RefMap& map, PremiseSet** prem)
{
  CALL("AIGRewriter::lev0Deref");

  static Stack<L0DerefQueryRec> queries;
  queries.reset();

  bool resNeg = false;

  for(;;) {

    bool neg = !r.polarity();
    if(neg) {
      resNeg = !resNeg;
      r = r.neg();
    }

    PremRef tgt;
    if(!map.find(r, tgt) || r==tgt.first) {
      break;
    }
    queries.push(L0DerefQueryRec(r,resNeg, tgt.second));
    ASS_LE(queries.size(), map.size());
    r = tgt.first;
  }

  if(queries.isNonEmpty()) {
    //we compress the dereference chain
    PremiseSet* premises =  queries.top().prems;
    queries.pop();
    while(queries.isNonEmpty()) {
      L0DerefQueryRec rec = queries.pop();
      premises = premises->getUnion(rec.prems);
      Ref toCache = (rec.neg==resNeg) ? r : r.neg();
      //DHMap::set returns false when overwriting
      NEVER(map.set(rec.aig, PremRef(toCache, premises)));
    }
    if(prem) {
      *prem = premises;
    }
  }
  else {
    if(prem) {
      *prem = PremiseSet::getEmpty();
    }
  }

  return resNeg ? r.neg() : r;
}

/**
 * (Iteratively) dereference parents of r in map
 *
 * r must be level 0 dereferenced.
 */
AIG::Ref AIGRewriter::lev1Deref(Ref r, RefMap& map, PremiseSet** prem)
{
  CALL("AIGRewriter::lev1Deref");
  ASS_EQ(r, lev0Deref(r, map, 0));

  bool neg = !r.polarity();
  if(neg) {
    r = r.neg();
  }

  Ref res;
  if(r.isAtom() || r.isTrue()) {
    res = r;
  }
  else if(r.isConjunction()) {
    Ref p1 = r.parent(0);
    Ref p2 = r.parent(1);
    PremiseSet* prem1;
    PremiseSet* prem2;
    Ref dp1 = lev0Deref(p1, map, &prem1);
    Ref dp2 = lev0Deref(p2, map, &prem2);
    if(p1==dp1 && p2==dp2) {
      res = r;
      if(prem) {
	*prem = PremiseSet::getEmpty();
      }
    }
    else {
      if(prem) {
	*prem = prem1->getUnion(prem2);
      }
      res = _aig.getConj(dp1, dp2);
    }
  }
  else {
    ASS(r.isQuantifier());

    Ref p = r.parent(0);
    Ref dp = lev0Deref(p, map, prem);
    if(p==dp) {
      res = r;
    }
    else {
      res = _aig.getQuant(false, r.getQuantifierVars(), dp);
    }
  }

  return neg ? res.neg() : res;
}

void AIGRewriter::collectUsed(Ref r, const RefMap& map, RefEdgeMap& edges)
{
  CALL("AIGRewriter::collectUsed");
  ASS(r.polarity());
  ASS(map.find(r));

  Ref rImg = map.get(r).first;

  static AIGInsideOutPosIterator ait;

  ait.reset(rImg);

  while(ait.hasNext()) {
    Ref p = ait.next();
    if(map.find(p) && p!=r) { //TODO: Make sure we don't want to include r itself among dependencies!
      LOG("pp_aigtr_sat_deps","dep: " << r << " <-- " << p);
      edges.pushToKey(r, p);
    }
  }
}

/**
 * @param map in/out, map that is restricted to become acyclic
 * @param domainOrder out parameter, will receive domain elements
 *        of the restricted map in topological order (nodes can refer
 *        only to items closer to the bottom of the stack).
 */
void AIGRewriter::restrictToGetOrderedDomain(RefMap& map, AIGStack& domainOrder)
{
  CALL("AIGRewriter::restrictToGetOrderedDomain");

  LOG("pp_aigtr_sat","ordering domain");

  static DHSet<Ref> seen;
  seen.reset();

  typedef MapToLIFOGraph<Ref> RefGraph;
  typedef Subgraph<RefGraph> RefSubgraph;
  RefGraph::Map edgeMap;

  VirtualIterator<Ref> domIt = map.domain();

  while(domIt.hasNext()) {
    Ref d = domIt.next();
    LOG("pp_aigtr_inp_map",d<<" --> "<<map.get(d).first);
    collectUsed(d, map, edgeMap);
  }

  RefGraph gr(edgeMap);
  gr.ensureNodes(map.domain());

  SCCAnalyzer<RefGraph> an0(gr);
  ScopedPtr<SCCAnalyzer<RefSubgraph> > an1;
  if(an0.breakingNodes().isNonEmpty()) {
    //if we have circular dependencies, we fix them by removing some mappings
    AIGStack::ConstIterator brIt(an0.breakingNodes());
    while(brIt.hasNext()) {
      Ref br = brIt.next();
      LOG("pp_aigtr_sat","domain element removed to break cycles: "<<br);
      map.remove(br);
    }
    Subgraph<RefGraph> subGr(gr, AIGStack::ConstIterator(an0.breakingNodes()));
    an1 = new SCCAnalyzer<RefSubgraph>(subGr);
  }

  const Stack<AIGStack>& comps = an1 ? an1->components() : an0.components();
  Stack<AIGStack>::BottomFirstIterator cit(comps);
  while(cit.hasNext()) {
    const AIGStack& comp = cit.next();
    ASS_EQ(comp.size(),1);
    domainOrder.push(comp.top());
    LOG("pp_aigtr_sat","domain element to process: "<<comp.top());
  }
}

/**
 * Apply @c map on @c r0 with caching (so that after the function returns,
 * map[r0] will be defined.
 *
 * To obtain predictable results, @c map (applied in a compositional
 * way) should be idempotent on @c r0.
 */
void AIGRewriter::applyWithCaching(Ref r0, RefMap& map)
{
  CALL("AIGRewriter::applyWithCaching");
  LOG("pp_aigtr_sat","applyWithCaching -- "<<r0);

  static AIGInsideOutPosIterator ait;
  ait.reset(r0);

  while(ait.hasNext()) {
    Ref r = ait.next();

    Ref dr0 = lev0Deref(r, map, 0);

    PremiseSet* l1DerefPrem;
    Ref dr1 = lev1Deref(dr0, map, &l1DerefPrem);
    if(r==dr1) {
      //nothing in the map applies
      continue;
    }
#if 1 //maybe it is not necessary to achieve the following condition:
    //if the node is dereferenced in the map, the parents of
    //the node should already be dereferenced as well
    ASS(r==dr0 || dr0==dr1);
#endif
    if(dr0==dr1) {
      ASS_EQ(map.get(r).first,dr1);
    }
    else {
      map.insert(r,PremRef(dr1, l1DerefPrem));
    }
  }
}

void AIGRewriter::makeIdempotent(RefMap& map, Stack<Ref>* finalDomain)
{
  CALL("AIGRewriter::makeIdempotent");

  static AIGStack order;
  order.reset();
  restrictToGetOrderedDomain(map, order);
  AIGStack::BottomFirstIterator cit(order);
  while(cit.hasNext()) {
    Ref r = cit.next();
    applyWithCaching(map.get(r).first, map);
    lev0Deref(r, map, 0); //collapse the rewritings
    if(finalDomain) {
      finalDomain->push(r);
    }
  }
}


void AIGRewriter::saturateOnTopSortedStack(const AIGStack& stack, RefMap& map)
{
  CALL("AIGRewriter::saturateOnTopSortedStack");

  unsigned idx = 0;
  //we have to iterate by indexes because the stack may be modified
  //and therefore we cannot use an iterator
  //(the stack may be modified as we can use _aig._orderedNodeRefs stack
  //where newly created nodes are added)
  for(size_t stack_idx = 0; stack_idx<stack.size(); stack_idx++) {
    Ref r = stack[stack_idx];
    ++idx;
    Ref dr0 = lev0Deref(r, map, 0);

    PremiseSet* l1DerefPrem;
    Ref dr1 = lev1Deref(dr0, map, &l1DerefPrem);
    if(r==dr1) {
      //nothing in the map applies
      continue;
    }
#if 1 //maybe it is not necessary to achieve the following condition:
    //if the node is dereferenced in the map, the parents of
    //the node should already be dereferenced as well
    ASS(r==dr0 || dr0==dr1);
#endif
    if(dr0==dr1) {
      ASS_EQ(map.get(r).first,dr1);
    }
    else {
      map.insert(r,PremRef(dr1,l1DerefPrem));
    }
  }
}


/**
 * Given map from AIG node --> AIG node, extend it to all nodes
 * that contain the given ones.
 * If map is not acyclic, remove some rewrites to make it acyclic.
 * Domain of map must only contain AIGRefs with positive polarity.
 *
 * @param finalDomain if non-zero, Refs that weren't eliminated from
 *                    the map wil be added into the stack.
 */
void AIGRewriter::saturateMap(RefMap& map, Stack<Ref>* finalDomain)
{
  CALL("AIGRewriter::saturateMap");
  ASS_REP(forAll(map.domain(), AIG::hasPositivePolarity), getFirstTrue(map.domain(), negPred(AIG::hasPositivePolarity)));

  makeIdempotent(map, finalDomain);

  saturateOnTopSortedStack(_aig._orderedNodeRefs, map);
}


}
