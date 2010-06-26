/**
 * @file SineUtils.cpp
 * Implements class SineUtils.
 */

#include <cmath>

#include "Lib/Deque.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/DHMultiset.hpp"
#include "Lib/Environment.hpp"
#include "Lib/List.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Set.hpp"
#include "Lib/TimeCounter.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SubformulaIterator.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"

#include "Options.hpp"
#include "Statistics.hpp"

#include "SineUtils.hpp"

#define SINE_PRINT_SELECTED 0

namespace Shell
{

using namespace Lib;
using namespace Kernel;

SineSymbolExtractor::SineSymbolExtractor()
{
  CALL("SineSymbolExtractor::SineSymbolExtractor");

  onSignatureChange();
}

/**
 * Should be called if there were new symbols added to the signature
 * since the construction of the object
 *
 * SymId corresponding to each symbol may change after a call to this function.
 */
void SineSymbolExtractor::onSignatureChange()
{
  CALL("SineSymbolExtractor::onSignatureChange");

  _funs=env.signature->functions();
  _preds=env.signature->predicates();
  _fnOfs=_preds;
}

/**
 * Return @b SymId that is greater than any @b SymId that can come from
 * the current problem
 *
 * The returned value is to be used to determine the size of various
 * arrays.
 */
SineSymbolExtractor::SymId SineSymbolExtractor::getSymIdBound()
{
  return env.signature->predicates() + env.signature->functions();
}

void SineSymbolExtractor::addSymIds(Literal* lit, int polarity, Stack<SymId>& ids) const
{
  CALL("SineSymbolExtractor::addSymIds");

  unsigned predFun=lit->functor();
  if(predFun<_preds) {
    ids.push(predFun);
  }

  NonVariableIterator nvi(lit);
  while(nvi.hasNext()) {
    Term* t=nvi.next().term();

    unsigned fun=t->functor();
    if(fun<_funs) {
      ids.push(_fnOfs+fun);
    }
  }
}

void SineSymbolExtractor::decodeSymId(SymId s, bool& pred, unsigned& functor)
{
  pred=s<_fnOfs;
  if(pred) {
    functor=s;
  }
  else {
    functor=s-_fnOfs;
  }
}

void SineSymbolExtractor::extractFormulaSymbols(Formula* f,int polarity,Stack<SymId>& itms)
{
  CALL("SineSymbolExtractor::extractFormulaSymbols");

  switch (f->connective()) {
    case LITERAL:
      addSymIds(f->literal(), polarity, itms);
      return;

    case AND:
    case OR: {
      FormulaList::Iterator fs(f->args());
      while (fs.hasNext()) {
	extractFormulaSymbols (fs.next(),polarity,itms);
      }
      return;
    }

    case IMP:
      extractFormulaSymbols (f->left(), -polarity, itms);
      extractFormulaSymbols (f->right(), polarity, itms);
      return;

    case NOT:
      extractFormulaSymbols (f->uarg(), -polarity, itms);
      return;

    case IFF:
    case XOR:
      extractFormulaSymbols (f->left(), 0, itms);
      extractFormulaSymbols (f->right(), 0, itms);
      return;

    case FORALL:
    case EXISTS:
      extractFormulaSymbols (f->qarg(), polarity, itms);
      return;

    case TRUE:
    case FALSE:
      return;
#if VDEBUG
    default:
      ASSERTION_VIOLATION;
      return;
#endif
  }
}

/**
 * Return iterator that yields SymIds of symbols in a unit.
 * Each SymId is yielded at most once.
 *
 * Only SymIds for symbols that were in the signature at the
 * time of the object construction or of the last call to the
 * @b onSignatureChange function are yielded.
 */
SineSymbolExtractor::SymIdIterator SineSymbolExtractor::extractSymIds(Unit* u)
{
  CALL("SineSymbolExtractor::extractSymIds");

  static Stack<SymId> itms;
  itms.reset();

  if(u->isClause()) {
    Clause* cl=static_cast<Clause*>(u);
    unsigned clen=cl->length();
    for(unsigned i=0;i<clen;i++) {
      Literal* lit=(*cl)[i];
      addSymIds(lit, 1, itms);
    }
  } else {
    FormulaUnit* fu=static_cast<FormulaUnit*>(u);
    extractFormulaSymbols(fu->formula(), 1, itms);
  }
  return pvi( getUniquePersistentIterator(Stack<SymId>::Iterator(itms)) );
}

void SineBase::initGeneralityFunction(UnitList* units)
{
  CALL("SineBase::initGeneralityFunction");

  SymId symIdBound=_symExtr.getSymIdBound();
  _gen.init(symIdBound,0);

  UnitList::Iterator uit(units);
  while(uit.hasNext()) {
    Unit* u=uit.next();
    SymIdIterator sit=_symExtr.extractSymIds(u);
    while(sit.hasNext()) {
      SymId sid=sit.next();
      _gen[sid]++;
    }
  }
}

SineSelector::SineSelector()
: _onIncluded(env.options->sineSelection()==Options::SS_INCLUDED),
  _genThreshold(env.options->sineGeneralityThreshold()),
  _tolerance(env.options->sineTolerance())
{
  CALL("SineSelector::SineSelector");
  ASS_GE(_tolerance, 1.0f);

  _strict=_tolerance==1.0f;
}

/**
 * Connect unit @b u with symbols it defines
 */
void SineSelector::updateDefRelation(Unit* u)
{
  CALL("SineSelector::updateDefRelation");

  SymIdIterator sit=_symExtr.extractSymIds(u);

  if(!sit.hasNext()) {
    _unitsWithoutSymbols.push(u);
    return;
  }

  static Stack<SymId> equalGenerality;
  equalGenerality.reset();

  SymId leastGenSym=sit.next();
  unsigned leastGenVal=_gen[leastGenSym];

  //it a symbol fits under _genThreshold, add it immediately [into the relation]
  if(leastGenVal<=_genThreshold) {
    UnitList::push(u,_def[leastGenSym]);
  }

  while(sit.hasNext()) {
    SymId sym=sit.next();
    unsigned val=_gen[sym];
    ASS_G(val,0);

    //it a symbol fits under _genThreshold, add it immediately [into the relation]
    if(val<=_genThreshold) {
      UnitList::push(u,_def[sym]);
    }

    if(val<leastGenVal) {
      leastGenSym=sym;
      leastGenVal=val;
      equalGenerality.reset();
    } else if(val==leastGenVal) {
      equalGenerality.push(sym);
    }
  }


  if(_strict) {
    //only if the least general symbol is over _genThreshold; otherwise it is already added
    if(leastGenVal>_genThreshold) {
      UnitList::push(u,_def[leastGenSym]);
      while(equalGenerality.isNonEmpty()) {
        UnitList::push(u,_def[equalGenerality.pop()]);
      }
    }
  }
  else {
    unsigned generalityLimit=static_cast<int>(leastGenVal*_tolerance);

    //if the generalityLimit is under _genThreshold, all suitable symbols are already added
    if(generalityLimit>_genThreshold) {
      sit=_symExtr.extractSymIds(u);
      while(sit.hasNext()) {
	SymId sym=sit.next();
	unsigned val=_gen[sym];
	//only if the symbol is over _genThreshold; otherwise it is already added
	if(val>_genThreshold && val<=generalityLimit) {
	  UnitList::push(u,_def[sym]);
	}
      }
    }
  }

}

void SineSelector::perform(UnitList*& units)
{
  CALL("SineSelector::perform");
  ASS_NEQ(env.options->sineSelection(),Options::SS_OFF);

  TimeCounter tc(TC_SINE_SELECTION);

  initGeneralityFunction(units);

  SymId symIdBound=_symExtr.getSymIdBound();

  Set<Unit*> selected;
  Stack<Unit*> selectedStack; //on this stack there are Units in the order they were selected
  Deque<Unit*> newlySelected;

  //build the D-relation and select the non-axiom formulas
  _def.init(symIdBound,0);
  UnitList::Iterator uit2(units);
  while(uit2.hasNext()) {
    Unit* u=uit2.next();
    bool performSelection= _onIncluded ? u->included() : (u->inputType()==Unit::AXIOM);
    if(performSelection) {
      updateDefRelation(u);
    }
    else {
      selected.insert(u);
      selectedStack.push(u);
      newlySelected.push_back(u);
    }
  }

  unsigned depthLimit=env.options->sineDepth();
  unsigned depth=0;
  newlySelected.push_back(0);

  //select required axiom formulas
  while(newlySelected.isNonEmpty()) {
    Unit* u=newlySelected.pop_front();

    if(!u) {
      //next selected formulas will be one step further from the original formulas
      depth++;
      if(depthLimit && depth==depthLimit) {
	break;
      }
      ASS(!depthLimit || depth<depthLimit);

      if(newlySelected.isNonEmpty()) {
	//we must push another mark if we're not done yet
	newlySelected.push_back(0);
      }
      continue;
    }

    SymIdIterator sit=_symExtr.extractSymIds(u);
    while(sit.hasNext()) {
      SymId sym=sit.next();
      UnitList::Iterator defUnits(_def[sym]);
      while(defUnits.hasNext()) {
	Unit* du=defUnits.next();
	if(selected.contains(du)) {
	  continue;
	}
	selected.insert(du);
	selectedStack.push(du);
	newlySelected.push_back(du);
      }
      //all defining units for the symbol sym were selected,
      //so we can remove them from the relation
      _def[sym]->destroy();
      _def[sym]=0;
    }
  }

  env.statistics->sineIterations=depth;

  env.statistics->selectedBySine=_unitsWithoutSymbols.size() + selectedStack.size();

  units->destroy();
  units=0;
  UnitList::pushFromIterator(Stack<Unit*>::Iterator(_unitsWithoutSymbols), units);
  while(selectedStack.isNonEmpty()) {
    UnitList::push(selectedStack.pop(), units);
  }

#if SINE_PRINT_SELECTED
  UnitList::Iterator selIt(units);
  while(selIt.hasNext()) {
    cout<<'#'<<selIt.next()->toString()<<endl;
  }
#endif
}

//////////////////////////////////////
// SineTheorySelector
//////////////////////////////////////

SineTheorySelector::SineTheorySelector()
: _genThreshold(env.options->sineGeneralityThreshold())
{
  CALL("SineTheorySelector::SineTheorySelector");
}

/**
 * Connect unit @b u with symbols it defines
 */
void SineTheorySelector::updateDefRelation(Unit* u)
{
  CALL("SineTheorySelector::updateDefRelation");

  SymIdIterator sit0=_symExtr.extractSymIds(u);

  if(!sit0.hasNext()) {
    _unitsWithoutSymbols.push(u);
    return;
  }

  static Stack<SymId> symIds;
  symIds.reset();
  symIds.loadFromIterator(sit0);

  Stack<SymId>::Iterator sit(symIds);

  ALWAYS(sit.hasNext());
  unsigned leastGenVal=_gen[sit.next()];

  while(sit.hasNext()) {
    SymId sym=sit.next();
    unsigned val=_gen[sym];
    ASS_G(val,0);

    if(val<leastGenVal) {
      leastGenVal=val;
    }
  }

  unsigned generalityLimit=leastGenVal*(maxTolerance/strictTolerance);

  Stack<SymId>::Iterator sit2(symIds);
  while(sit2.hasNext()) {
    SymId sym=sit2.next();
    unsigned val=_gen[sym];

    if(val<=_genThreshold) {
      //if a symbol fits under _genThreshold, add it into the relation
      DEntryList::push(DEntry(strictTolerance,u),_def[sym]);
    }
    else if(val<=generalityLimit) {
      unsigned short minTolerance=(val*strictTolerance)/leastGenVal;
      //only if the symbol is over _genThreshold; otherwise it is already added
      DEntryList::push(DEntry(minTolerance,u),_def[sym]);
    }
  }

}

/**
 * Preprocess the theory axioms in @b units, so that some of them can be later
 * selected for a particular problem formulas by the @b addSelectedAxioms() function
 *
 * If the value of the sineTolerance and sineDepth options changes after the
 * preprocessing and before the call to the @b addSelectedAxioms function, the
 * modified values will be used (The preprocessing allows for selection with
 * tolerance values up to the limit implied by the value of @b maxTolerance.)
 */
void SineTheorySelector::initSelectionStructure(UnitList* units)
{
  CALL("SineTheorySelector::initSelectionStructure");

  TimeCounter tc(TC_SINE_SELECTION);

  initGeneralityFunction(units);

  SymId symIdBound=_symExtr.getSymIdBound();

  //build the D-relation and select the non-axiom formulas
  _def.init(symIdBound,0);
  UnitList::Iterator uit(units);
  while(uit.hasNext()) {
    Unit* u=uit.next();
    updateDefRelation(u);
  }
}

/**
 * Modify the @b units list so that it contains units selectedby the SInE
 * axiom selection algorithm from the units passed to the @b initSelectionStructure()
 * function.
 *
 * None of the units passed to the @b initSelectionStructure() function should
 * appear in the @b units list passed as an argument.
 */
void SineTheorySelector::addSelectedAxioms(UnitList*& units)
{
  CALL("SineTheorySelector::addSelectedAxioms");

  unsigned short intTolerance=static_cast<unsigned short>(ceil(env.options->sineTolerance()*10));

  DHSet<SymId> addedSymIds;
  DHSet<Unit*> selected; //selected units without the original problem units
  Deque<Unit*> newlySelected;

  newlySelected.pushBackFromIterator(UnitList::Iterator(units));

  unsigned depthLimit=env.options->sineDepth();
  unsigned depth=0;
  newlySelected.push_back(0);

  //select required axiom formulas
  while(newlySelected.isNonEmpty()) {
    Unit* u=newlySelected.pop_front();

    if(!u) {
      //next selected formulas will be one step further from the original formulas
      depth++;
      if(depthLimit && depth==depthLimit) {
	break;
      }
      ASS(!depthLimit || depth<depthLimit);

      if(newlySelected.isNonEmpty()) {
	//we must push another mark if we're not done yet
	newlySelected.push_back(0);
      }
      continue;
    }

    SymIdIterator sit=_symExtr.extractSymIds(u);
    while(sit.hasNext()) {
      SymId sym=sit.next();
      if(!addedSymIds.insert(sym)) {
	//we already added units belonging to this symbol
	continue;
      }
      DEntryList::Iterator defUnits(_def[sym]);
      while(defUnits.hasNext()) {
	DEntry de=defUnits.next();

	if(de.minTolerance>intTolerance || !selected.insert(de.unit)) {
	  continue;
	}
	UnitList::push(de.unit, units);
	newlySelected.push_back(de.unit);
      }
    }
  }

  UnitList::pushFromIterator(Stack<Unit*>::Iterator(_unitsWithoutSymbols), units);

  env.statistics->sineIterations=depth;
  env.statistics->selectedBySine=_unitsWithoutSymbols.size() + selected.size();

#if SINE_PRINT_SELECTED
  UnitList::Iterator selIt(units);
  while(selIt.hasNext()) {
    cout<<'#'<<selIt.next()->toString()<<endl;
  }
#endif
}


}
