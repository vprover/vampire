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

#include "Shell/AnswerLiteralManager.hpp"
#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "URResolution.hpp"

namespace Inferences
{

using namespace std;
using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

URResolution::URResolution(bool full)
: _full(full), _selectedOnly(false), _unitIndex(0), _nonUnitIndex(0) {}

/**
 * Creates URResolution object with explicitely supplied
 * settings and indexes
 *
 * For objects created using this constructor it is not allowed
 * to call the @c attach() function.
 */
URResolution::URResolution(bool full, bool selectedOnly, UnitClauseLiteralIndex* unitIndex,
    NonUnitClauseLiteralIndex* nonUnitIndex)
: _full(full), _emptyClauseOnly(false), _selectedOnly(selectedOnly), _unitIndex(unitIndex), _nonUnitIndex(nonUnitIndex) {}

void URResolution::attach(SaturationAlgorithm* salg)
{
  ASS(!_unitIndex);
  ASS(!_nonUnitIndex);

  GeneratingInferenceEngine::attach(salg);

  bool synthesis = (env.options->questionAnswering() == Options::QuestionAnsweringMode::SYNTHESIS);

  _unitIndex = static_cast<UnitClauseLiteralIndex*> ( synthesis
    ? _salg->getIndexManager()->request(URR_UNIT_CLAUSE_WITH_AL_SUBST_TREE)
    : _salg->getIndexManager()->request(URR_UNIT_CLAUSE_SUBST_TREE) );
  _nonUnitIndex = static_cast<NonUnitClauseLiteralIndex*> ( synthesis
	  ? _salg->getIndexManager()->request(URR_NON_UNIT_CLAUSE_WITH_AL_SUBST_TREE)
    : _salg->getIndexManager()->request(URR_NON_UNIT_CLAUSE_SUBST_TREE) );

  Options::URResolution optSetting = _salg->getOptions().unitResultingResolution();
  ASS_NEQ(optSetting,  Options::URResolution::OFF);
  _emptyClauseOnly = optSetting==Options::URResolution::EC_ONLY;
}

void URResolution::detach()
{
  _unitIndex = 0;
  _nonUnitIndex = 0;
  if (env.options->questionAnswering() == Options::QuestionAnsweringMode::SYNTHESIS) {
    _salg->getIndexManager()->release(URR_UNIT_CLAUSE_WITH_AL_SUBST_TREE);
    _salg->getIndexManager()->release(URR_NON_UNIT_CLAUSE_WITH_AL_SUBST_TREE);
  } else {
    _salg->getIndexManager()->release(URR_UNIT_CLAUSE_SUBST_TREE);
    _salg->getIndexManager()->release(URR_NON_UNIT_CLAUSE_SUBST_TREE);
  }
  GeneratingInferenceEngine::detach();
}

struct URResolution::Item
{
  USE_ALLOCATOR(URResolution::Item);

  Item(Clause* cl, bool selectedOnly, URResolution& parent, bool mustResolveAll)
  : _orig(cl), _color(cl->color()), _parent(parent)
  {
    unsigned clen = cl->length();
    bool synthesis = (env.options->questionAnswering() == Options::QuestionAnsweringMode::SYNTHESIS);
    _ansLit = synthesis ? cl->getAnswerLiteral() : nullptr;
    _mustResolveAll = mustResolveAll || (selectedOnly ? true : (clen < 2 + (_ansLit ? 1 : 0)));
    unsigned litslen = clen - (_ansLit ? 1 : 0);
    _premises.init(litslen, 0);
    _lits.reserve(litslen);
    unsigned nonGroundCnt = 0;
    for(unsigned i=0; i<clen; i++) {
      if(!(*cl)[i]->ground()) nonGroundCnt++;
      if ((*cl)[i] != _ansLit) {
        _lits.push((*cl)[i]);
        if(!_lits.top()->ground()) nonGroundCnt++;
      }
    }
    _atMostOneNonGround = nonGroundCnt<=1;

    _activeLength = selectedOnly ? cl->numSelected() : litslen;
    ASS_REP2(_activeLength>=litslen-1, cl->toString(), cl->numSelected());
  }

  /**
   * Resolve away @c idx -th literal of the clause. This involves
   * applying the substitution in @c unif to all remaining literals.
   * If @c useQuerySubstitution is true, the query part of the
   * substitution is applied to the literals, otherwise the result
   * part is applied.
   */
  bool resolveLiteral(unsigned idx, QueryRes<ResultSubstitutionSP, LiteralClause>& unif, Clause* premise, bool useQuerySubstitution, bool ansLitIte)
  {
    if (_ansLit && !_ansLit->ground()) {
      _ansLit = unif.unifier->apply(_ansLit, !useQuerySubstitution);
    }
    Literal* premAnsLit = nullptr;
    bool synthesis = (env.options->questionAnswering() == Options::QuestionAnsweringMode::SYNTHESIS);
    if (synthesis && premise->hasAnswerLiteral()) {
      premAnsLit = premise->getAnswerLiteral();
      if (!premAnsLit->ground()) {
        premAnsLit = unif.unifier->apply(premAnsLit, useQuerySubstitution);
      }
    }
    if (ansLitIte && (!_ansLit || !premAnsLit || (_ansLit == premAnsLit))) {
      return false;
    }
    Literal* rlit = _lits[idx];
    _lits[idx] = 0;
    _premises[idx] = premise;
    _color = static_cast<Color>(_color | premise->color());
    ASS_NEQ(_color, COLOR_INVALID)

    RobSubstitution rSubst;
    bool substUsed = false;
    if (synthesis && premise->hasAnswerLiteral()) {
      if (!_ansLit) {
        _ansLit = premAnsLit;
      } else if (_ansLit != premAnsLit) {
        if (!ansLitIte && rSubst.unifyArgs(_ansLit, 0, premAnsLit, 0)) {
          _ansLit = rSubst.apply(_ansLit, 0);
          substUsed = true;
        } else {
          bool neg = rlit->isNegative();
          Literal* resolved = unif.unifier->apply(rlit, !useQuerySubstitution);
          if (neg) {
            resolved = Literal::complementaryLiteral(resolved);
          }
          _ansLit = AnswerLiteralManager::getInstance()->makeITEAnswerLiteral(resolved, neg ? _ansLit : premAnsLit, neg ? premAnsLit : _ansLit);
        }
      }
    }

    if(_atMostOneNonGround) {
      return true;
    }

    unsigned nonGroundCnt = _ansLit ? !_ansLit->ground() : 0;
    unsigned clen = _lits.size();
    for(unsigned i=0; i<clen; i++) {
      Literal*& lit = _lits[i];
      if(!lit) {
        continue;
      }
      lit = unif.unifier->apply(lit, !useQuerySubstitution);
      if (substUsed) lit = rSubst.apply(lit, 0);
      if(!lit->ground()) {
        nonGroundCnt++;
      }
    }
    _atMostOneNonGround = nonGroundCnt<=1;
    return true;
  }

  Clause* generateClause() const
  {
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

    LiteralIterator it = _ansLit ? pvi(getSingletonIterator(_ansLit)) : LiteralIterator::getEmpty();
    if(single) {
      if (!_ansLit || _ansLit->ground()) {
        single = Renaming::normalize(single);
      }
      res = Clause::fromIterator(concatIters(getSingletonIterator(single), it), inf);
    }
    else {
      res = Clause::fromIterator(it, inf);
    }
    return res;
  }

  int getGoodness(Literal* lit)
  {
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
  Stack<Literal*> _lits;

  Literal* _ansLit;

  unsigned _activeLength;
  URResolution& _parent;
};

/**
 * Perform one level of the BFS traversal of possible resolution
 * sequences
 *
 * (See documentation to the @c processAndGetClauses() function.)
 */
void URResolution::processLiteral(ItemList*& itms, unsigned idx, bool ansLitIte)
{
  bool synthesis = (env.options->questionAnswering() == Options::QuestionAnsweringMode::SYNTHESIS);
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

    auto unifs = _unitIndex->getUnifications(lit, true, true);
    while(unifs.hasNext()) {
      auto unif = unifs.next();

      if( !ColorHelper::compatible(itm->_color, unif.data->clause->color()) ) {
        continue;
      }

      Item* itm2 = new Item(*itm);
      if (!itm2->resolveLiteral(idx, unif, unif.data->clause, true, ansLitIte)) {
        continue;
      }
      iit.insert(itm2);

      if(!_full && itm->_atMostOneNonGround && (!synthesis || !unif.data->clause->hasAnswerLiteral())) {
        /* if there is only one non-ground literal left, there is no need to retrieve all unifications.
           However, this does not hold under AVATAR where different empty clauses may close different
           splitting branches, that's why only "full" URR is complete under AVATAR (see Options::complete)
        */
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
void URResolution::processAndGetClauses(Item* itm, unsigned startIdx, ClauseList*& acc, bool ansLitIte)
{
  unsigned activeLen = itm->_activeLength;

  ItemList* itms = 0;
  ItemList::push(itm, itms);
  for(unsigned i = startIdx; itms && i<activeLen; i++) {
    processLiteral(itms, i, ansLitIte);
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
void URResolution::doBackwardInferences(Clause* cl, ClauseList*& acc, bool ansLitIte)
{
  ASS((cl->size() == 1) || (cl->size() == 2 && cl->hasAnswerLiteral()));

  Literal* lit = (*cl)[0];
  if (lit->isAnswerLiteral()) {
    lit = (*cl)[1];
  }

  auto unifs = _nonUnitIndex->getUnifications(lit, true, true);
  while(unifs.hasNext()) {
    auto unif = unifs.next();
    Clause* ucl = unif.data->clause;

    if( !ColorHelper::compatible(cl->color(), ucl->color()) ) {
      continue;
    }

    Item* itm = new Item(ucl, _selectedOnly, *this, _emptyClauseOnly);
    unsigned pos;
    if (!itm->_ansLit) {
      pos = ucl->getLiteralPosition(unif.data->literal);
    } else {
      for (unsigned i = 0; i < itm->_lits.size(); ++i) {
        if (itm->_lits[i] == unif.data->literal) {
          pos = i;
          break;
        }
      }
    }
    ASS(!_selectedOnly || pos<ucl->numSelected());
    swap(itm->_lits[0], itm->_lits[pos]);
    if (itm->resolveLiteral(0, unif, cl, /* useQuerySubstitution */ false, ansLitIte)) {
      processAndGetClauses(itm, 1, acc, ansLitIte);
    }
  }
}

ClauseIterator URResolution::generateClauses(Clause* cl)
{
  unsigned clen = cl->size();
  if(clen<1) {
    return ClauseIterator::getEmpty();
  }

  TIME_TRACE("unit resulting resolution");

  ClauseList* res = 0;
  processAndGetClauses(new Item(cl, _selectedOnly, *this, _emptyClauseOnly), 0, res, false);
  processAndGetClauses(new Item(cl, _selectedOnly, *this, _emptyClauseOnly), 0, res, true);

  if (clen==1 ||
      ((env.options->questionAnswering() == Options::QuestionAnsweringMode::SYNTHESIS) && clen==2 && cl->hasAnswerLiteral())) {
    doBackwardInferences(cl, res, false);
    doBackwardInferences(cl, res, true);
  }

  return getPersistentIterator(ClauseList::DestructiveIterator(res));
}

}
