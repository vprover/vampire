/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file URResolution.cpp
 * Implements class URResolution.
 */

#include "Lib/DArray.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/PairUtils.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/ColorHelper.hpp"
#include "Kernel/Renaming.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/SortHelper.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/LiteralIndex.hpp"
#include "Indexing/IndexManager.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "URResolution.hpp"

namespace Inferences
{

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

URResolution::URResolution()
: _selectedOnly(false), _unitIndex(0), _nonUnitIndex(0) {}

/**
 * Creates URResolution object with explicitely supplied
 * settings and indexes
 *
 * For objects created using this constructor it is not allowed
 * to call the @c attach() function.
 */
URResolution::URResolution(bool selectedOnly, UnitClauseLiteralIndex* unitIndex,
    NonUnitClauseLiteralIndex* nonUnitIndex)
: _emptyClauseOnly(false), _selectedOnly(selectedOnly), _unitIndex(unitIndex), _nonUnitIndex(nonUnitIndex) {}

void URResolution::attach(SaturationAlgorithm* salg)
{
  CALL("URResolution::attach");
  ASS(!_unitIndex);
  ASS(!_nonUnitIndex);

  GeneratingInferenceEngine::attach(salg);

  _unitIndex = static_cast<UnitClauseLiteralIndex*> (
	  _salg->getIndexManager()->request(GENERATING_UNIT_CLAUSE_SUBST_TREE) );
  _nonUnitIndex = static_cast<NonUnitClauseLiteralIndex*> (
	  _salg->getIndexManager()->request(GENERATING_NON_UNIT_CLAUSE_SUBST_TREE) );

  Options::URResolution optSetting = _salg->getOptions().unitResultingResolution();
  ASS_NEQ(optSetting,  Options::URResolution::OFF);
  _emptyClauseOnly = optSetting==Options::URResolution::EC_ONLY;
}

void URResolution::detach()
{
  CALL("URResolution::detach");

  _unitIndex = 0;
  _salg->getIndexManager()->release(GENERATING_UNIT_CLAUSE_SUBST_TREE);
  _nonUnitIndex = 0;
  _salg->getIndexManager()->release(GENERATING_NON_UNIT_CLAUSE_SUBST_TREE);
  GeneratingInferenceEngine::detach();
}

struct URResolution::Item
{
  CLASS_NAME(URResolution::Item);
  USE_ALLOCATOR(URResolution::Item); 
  
  Item(Clause* cl, bool selectedOnly, URResolution& parent, bool mustResolveAll)
  : _mustResolveAll(mustResolveAll || (selectedOnly ? true : (cl->length() < 2)) ), _orig(cl), _color(cl->color()),
    _parent(parent)
  {
    CALL("URResolution::Item::Item");

    unsigned clen = cl->length();
    _premises.init(clen, 0);
    _lits.ensure(clen);
    unsigned nonGroundCnt = 0;
    for(unsigned i=0; i<clen; i++) {
      _lits[i] = (*cl)[i];
      if(!_lits[i]->ground()) {
        nonGroundCnt++;
      }
    }
    _atMostOneNonGround = nonGroundCnt<=1;

    _activeLength = selectedOnly ? cl->numSelected() : clen;
//    ASS_GE(_activeLength, clen-1);
    ASS_REP2(_activeLength>=clen-1, cl->toString(), cl->numSelected());
  }

  /**
   * Resolve away @c idx -th literal of the clause. This involves
   * applying the substitution in @c unif to all remaining literals.
   * If @c useQuerySubstitution is true, the query part of the
   * substitution is applied to the literals, otherwise the result
   * part is applied.
   */
  void resolveLiteral(unsigned idx, SLQueryResult& unif, Clause* premise, bool useQuerySubstitution)
  {
    CALL("URResolution::Item::resolveLiteral");

    _lits[idx] = 0;
    _premises[idx] = premise;
    _color = static_cast<Color>(_color | premise->color());
    ASS_NEQ(_color, COLOR_INVALID)

    if(_atMostOneNonGround) {
      return;
    }

    unsigned nonGroundCnt = 0;
    unsigned clen = _lits.size();
    for(unsigned i=0; i<clen; i++) {
      Literal*& lit = _lits[i];
      if(!lit) {
        continue;
      }
      lit = unif.substitution->apply(lit, !useQuerySubstitution);
      if(!lit->ground()) {
        nonGroundCnt++;
      }
    }
    _atMostOneNonGround = nonGroundCnt<=1;
  }

  Clause* generateClause() const
  {
    CALL("URResolution::Item::generateClause");

    UnitList* premLst = 0;
    UnitList::push(_orig, premLst);
    Literal* single = 0;
    unsigned clen = _lits.size();
    for(unsigned i=0; i<clen; i++) {
      if(_lits[i]!=0) {
        ASS_EQ(single,0);
        ASS_EQ(_premises[i],0);
        single = _lits[i];
      }
      else {
        Clause* premise = _premises[i];
        ASS(premise);
        UnitList::push(premise, premLst);
      }
    }

    Inference inf(GeneratingInferenceMany(InferenceRule::UNIT_RESULTING_RESOLUTION, premLst));
    Clause* res;

    if(single) {
      single = Renaming::normalize(single);
      res = Clause::fromIterator(getSingletonIterator(single), inf);
    }
    else {
      res = Clause::fromIterator(LiteralIterator::getEmpty(), inf);
    }
    return res;
  }

  int getGoodness(Literal* lit)
  {
    CALL("URResolution::Item::getGoodness");

    return lit->weight() - lit->getDistinctVars();
  }

  /**
   * From among the remaining literals (i.e. those with index at
   * least @c idx), select the one most suitable for resolving
   * (according to the @c getGoodness() function) and move it to
   * the @c idx position (so that it is resolved next).
   */
  void getBestLiteralReady(unsigned idx)
  {
    CALL("URResolution::Item::getBestLiteralReady");

    ASS_L(idx, _activeLength);

    unsigned choiceSize = _activeLength - idx;
    if(choiceSize==1) {
      return;
    }

    unsigned bestIdx = idx;
    ASS(_lits[bestIdx]);
    int bestVal = getGoodness(_lits[bestIdx]);

    for(unsigned i=idx+1; i<_activeLength; i++) {
      ASS(_lits[i]);
      int val = getGoodness(_lits[i]);
      if(val>bestVal) {
        bestVal = val;
        bestIdx = i;
      }
    }
    if(idx!=bestIdx) {
      swap(_lits[idx], _lits[bestIdx]);
    }
  }

  /** If true, we may skip resolving one of the remaining literals */
  bool _mustResolveAll;

  /** All remaining literals except for one are ground */
  bool _atMostOneNonGround;

  /** The original clause we are resolving */
  Clause* _orig;

  Color _color;

  /** Premises used to resolve away particular literals */
  DArray<Clause*> _premises;

  /** Unresolved literals, or zeroes at positions of the resolved ones
   *
   * The unresolved literals have the substitutions from other resolutions
   * applied to themselves */
  DArray<Literal*> _lits;

  unsigned _activeLength;
  URResolution& _parent;
};

/**
 * Perform one level of the BFS traversal of possible resolution
 * sequences
 *
 * (See documentation to the @c processAndGetClauses() function.)
 */
void URResolution::processLiteral(ItemList*& itms, unsigned idx)
{
  CALL("URResolution::processLiteral");

  ItemList::DelIterator iit(itms);
  while(iit.hasNext()) {
    Item* itm = iit.next();
    itm->getBestLiteralReady(idx);
    Literal* lit = itm->_lits[idx];
    ASS(lit);

    if(!itm->_mustResolveAll) {
      Item* itm2 = new Item(*itm);
      itm2->_mustResolveAll = true;
      iit.insert(itm2);
    }

    SLQueryResultIterator unifs = _unitIndex->getUnifications(lit, true, true);
    while(unifs.hasNext()) {
      SLQueryResult unif = unifs.next();

      if( !ColorHelper::compatible(itm->_color, unif.clause->color()) ) {
        continue;
      }

      Item* itm2 = new Item(*itm);
      itm2->resolveLiteral(idx, unif, unif.clause, true);
      iit.insert(itm2);

      if(itm->_atMostOneNonGround) {
        //if there is only one non-ground literal left, there is no need to retrieve
        //all unifications
        break;
      }
    }

    iit.del();
    delete itm;
  }
}

/**
 * Explore possible ways of resolving away literals in @c itm,
 * and from the successful ones add the resulting clause into
 * @c acc. The search starts at literal with index @c startIdx.
 *
 * What we do is a BFS traversal of all possible resolutions
 * on the clause represented in @c itm. In the @c itms list we
 * store all elements of @c i -th level of the search, and a
 * call to the @c processLiteral() function moves us to the next
 * level of the traversal.
 */
void URResolution::processAndGetClauses(Item* itm, unsigned startIdx, ClauseList*& acc)
{
  CALL("URResolution::processAndGetClauses");

  unsigned activeLen = itm->_activeLength;

  ItemList* itms = 0;
  ItemList::push(itm, itms);
  for(unsigned i = startIdx; itms && i<activeLen; i++) {
    processLiteral(itms, i);
  }

  while(itms) {
    Item* itm = ItemList::pop(itms);
    ClauseList::push(itm->generateClause(), acc);
    env.statistics->urResolution++;
    delete itm;
  }
}

/**
 * Perform URR inferences between a newly derived unit clause
 * @c cl and non-unit active clauses
 */
void URResolution::doBackwardInferences(Clause* cl, ClauseList*& acc)
{
  CALL("URResolution::doBackwardInferences");
  ASS_EQ(cl->size(), 1);

  Literal* lit = (*cl)[0];

  SLQueryResultIterator unifs = _nonUnitIndex->getUnifications(lit, true, true);
  while(unifs.hasNext()) {
    SLQueryResult unif = unifs.next();
    Clause* ucl = unif.clause;

    if( !ColorHelper::compatible(cl->color(), ucl->color()) ) {
      continue;
    }

    Item* itm = new Item(ucl, _selectedOnly, *this, _emptyClauseOnly);
    unsigned pos = ucl->getLiteralPosition(unif.literal);
    ASS(!_selectedOnly || pos<ucl->numSelected());
    swap(itm->_lits[0], itm->_lits[pos]);
    itm->resolveLiteral(0, unif, cl, false);

    processAndGetClauses(itm, 1, acc);
  }
}

ClauseIterator URResolution::generateClauses(Clause* cl)
{
  CALL("URResolution::generateClauses");

  unsigned clen = cl->size();
  if(clen<1) {
    return ClauseIterator::getEmpty();
  }

  TimeCounter tc(TC_UR_RESOLUTION);

  ClauseList* res = 0;
  processAndGetClauses(new Item(cl, _selectedOnly, *this, _emptyClauseOnly), 0, res);

  if(clen==1) {
    doBackwardInferences(cl, res);
  }

  return getPersistentIterator(ClauseList::DestructiveIterator(res));
}

}
