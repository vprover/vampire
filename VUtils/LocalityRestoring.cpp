/**
 * @file LocalityRestoring.cpp
 * Implements class LocalityRestoring.
 */

#include "Lib/Environment.hpp"

#include "Kernel/FormulaUnit.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SubformulaIterator.hpp"
#include "Kernel/TermIterators.hpp"

#include "LocalityRestoring.hpp"

namespace VUtils
{

LocalityRestoring::LocalityRestoring(Stack<Unit*>& derivation, Stack<Unit*>& target)
: _der(derivation), _tgt(target)
{
  CALL("LocalityRestoring::LocalityRestoring");

  unsigned dlen = derivation.length();
  for(unsigned i=0; i<dlen; i++) {
    _unitIndexes.insert(_der[i], i);
  }

  discoverColors();
  ASS_EQ(_colors.size(), _der.size());
  ASS_EQ(_nonLocal.size(), _der.size());
}

bool LocalityRestoring::perform()
{
  CALL("LocalityRestoring::perform");

  if(_allLocal) {
    _tgt = _der;
    return true;
  }
  return false;
}

bool LocalityRestoring::isLocal(Unit* u)
{
  unsigned uidx = _unitIndexes.get(u);

  Color clr = _colors[uidx];

  if(clr==COLOR_INVALID) {
    return false;
  }

  UnitSpecIterator parIt = InferenceStore::instance()->getParents(UnitSpec(u));
  while(parIt.hasNext()) {
    Unit* par = parIt.next().unit();
    unsigned pidx = _unitIndexes.get(par);
    Color pclr = _colors[pidx];
    if(pclr!=COLOR_TRANSPARENT && pclr!=clr) {
      if(clr==COLOR_TRANSPARENT) {
	clr = pclr;
      }
      if(pclr!=clr) {
	return false;
      }
    }
  }
  return clr!=COLOR_INVALID;
}

void LocalityRestoring::discoverColors()
{
  CALL("LocalityRestoring::discoverColors");

  _allLocal = true;

  Stack<Unit*>::BottomFirstIterator uit(_der);
  while(uit.hasNext()) {
    Unit* u = uit.next();
    Color unitColor = getColor(u);
//    if(unitColor==COLOR_INVALID) { LOGV(u->toString()); }
    _colors.push(unitColor);

    bool local = isLocal(u);
    _allLocal &= local;
    _nonLocal.push(!local);
//    if(u->number()==308 || u->number()==307) { LOG(unitColor<<" "<<u->toString()); }
  }
}

/**
 * Return color of the unit.
 *
 * This function doesn't regard the color of predicates.
 *
 * If there are both colors, COLOR_INVALID is returned.
 */
Color LocalityRestoring::getColor(Unit* u)
{
  CALL("LocalityRestoring::violatesColors");
  ASS(!u->isClause());

  FormulaUnit* fu = static_cast<FormulaUnit*>(u);

  Color unitColor = COLOR_TRANSPARENT;

  SubformulaIterator sfit(fu->formula());
  while(sfit.hasNext()) {
    Formula* sf = sfit.next();
    if(sf->connective()!=LITERAL) {
      continue;
    }
    Literal* lit = sf->literal();

    SubtermIterator stit(lit);
    while(stit.hasNext()) {
      TermList trm = stit.next();
      if(!trm.isTerm()) {
	continue;
      }
      unsigned func = trm.term()->functor();
      Color tColor = env.signature->getFunction(func)->color();
      if(tColor!=COLOR_TRANSPARENT) {
	if(unitColor==COLOR_TRANSPARENT) {
	  unitColor = tColor;
	}
	if(unitColor!=tColor) {
	  return COLOR_INVALID;
	}
      }
    }
  }
  return unitColor;
}

void LocalityRestoring::extractComponents()
{

}


}
