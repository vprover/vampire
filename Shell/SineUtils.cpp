/**
 * @file SineUtils.cpp
 * Implements class SineUtils.
 */

#include "../Lib/DHMultiset.hpp"
#include "../Lib/Environment.hpp"
#include "../Lib/List.hpp"
#include "../Lib/Metaiterators.hpp"
#include "../Lib/Set.hpp"
#include "../Lib/VirtualIterator.hpp"

#include "../Kernel/Clause.hpp"
#include "../Kernel/FormulaUnit.hpp"
#include "../Kernel/Signature.hpp"
#include "../Kernel/SubformulaIterator.hpp"
#include "../Kernel/Term.hpp"
#include "../Kernel/TermFunIterator.hpp"

#include "Options.hpp"
#include "Statistics.hpp"

#include "SineUtils.hpp"

#define SINE_PRINT_SELECTED 0

namespace Shell
{

using namespace Lib;
using namespace Kernel;


SineSelector::SineSelector()
: _onIncluded(env.options->sineSelection()==Options::SS_INCLUDED),
  _genThreshold(env.options->sineGeneralityThreshold()),
  _benevolence(env.options->sineBenevolence()),
  _fnOfs(env.signature->predicates())
{
  CALL("SineSelector::SineSelector");
  ASS_NEQ(env.options->sineSelection(),Options::SS_OFF);
  ASS_GE(_benevolence, 1.0f);

  _strict=_benevolence==1.0f;
}

/**
 * Return @b SymId that is greater than any @b SymId that can come from
 * the current problem
 *
 * The returned value is to be used to determine the size of various
 * arrays.
 */
SineSelector::SymId SineSelector::getSymIdBound()
{
  return env.signature->predicates() + env.signature->functions();
}

SineSelector::SymId SineSelector::getSymId(Literal* lit, bool polarity)
{
//  return lit->functor()*2 + (polarity^lit->isNegative()?0:1);
  return lit->functor();
}
SineSelector::SymId SineSelector::getSymId(Term* t)
{
  ASS(!t->isLiteral());
  return _fnOfs+t->functor();
}

struct SineSelector::FunctionSymIdFn
{
  FunctionSymIdFn(SineSelector* ss) : _ss(ss) {}
  DECL_RETURN_TYPE(SymId);
  SymId operator()(TermList t)
  {
    ASS(t.isTerm());
    return _ss->getSymId(t.term());
  }

  SineSelector* _ss;
};


void SineSelector::extractFormulaSymbols(Formula* f,int polarity,Stack<SymId>& itms)
{
  CALL("SineSelector::extractFormulaSymbols");

  switch (f->connective()) {
    case LITERAL:
    {
      Literal* lit=f->literal();

      switch(polarity) {
      case -1:
	itms.push( getSymId(lit, false) );
	break;
      case 0:
	itms.push( getSymId(lit, true) );
	itms.push( getSymId(lit, false) );
	break;
      case 1:
	itms.push( getSymId(lit, true) );
	break;
#if VDEBUG
      default:
	ASSERTION_VIOLATION;
#endif
      }

      itms.pushFromIterator( getMappingIterator(
		    vi( new Term::NonVariableIterator(lit) ),
		    FunctionSymIdFn(this)) );
      return;
    }

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
 * Return iterator that yields SymIds of all symbols in a unit.
 * Each SymId is yielded at most once.
 */
SineSelector::SymIdIterator SineSelector::extractSymIds(Unit* u)
{
  CALL("SineSelector::extractSymIds");

  Stack<SymId> itms;
  if(u->isClause()) {
    Clause* cl=static_cast<Clause*>(u);
    unsigned clen=cl->length();
    for(unsigned i=0;i<clen;i++) {
      Literal* lit=(*cl)[i];
      itms.push( getSymId(lit, true) );
      itms.pushFromIterator( getMappingIterator(
		    vi( new Term::NonVariableIterator(lit) ),
		    FunctionSymIdFn(this)) );
    }
  } else {
    FormulaUnit* fu=static_cast<FormulaUnit*>(u);
    extractFormulaSymbols(fu->formula(), 1, itms);
  }
  return pvi( getUniquePersistentIterator(Stack<SymId>::Iterator(itms)) );
}

/**
 * Connect unit @b u with symbols it defines
 */
void SineSelector::updateDefRelation(Unit* u)
{
  CALL("SineSelector::updateDefRelation");

  SymIdIterator sit=extractSymIds(u);

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
    unsigned generalityLimit=static_cast<int>(leastGenVal*_benevolence);

    //if the generalityLimit is under _genThreshold, all suitable symbols are already added
    if(generalityLimit>_genThreshold) {
      sit=extractSymIds(u);
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

  SymId symIdBound=getSymIdBound();

  //determine symbol generality
  _gen.init(symIdBound,0);
  UnitList::Iterator uit1(units);
  while(uit1.hasNext()) {
    Unit* u=uit1.next();
    SymIdIterator sit=extractSymIds(u);
    while(sit.hasNext()) {
      SymId sid=sit.next();
      _gen[sid]++;
    }
  }

  Set<Unit*> selected;
  Stack<Unit*> selectedStack; //on this stack there are Units in the order they were selected
  Stack<Unit*> newlySelected;

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
      newlySelected.push(u);
    }
  }


  //select required axiom formulas
  while(newlySelected.isNonEmpty()) {
    Unit* u=newlySelected.pop();
    SymIdIterator sit=extractSymIds(u);
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
	newlySelected.push(du);
      }
      //all defining units for the symbol sym were selected,
      //so we can remove them from the relation
      _def[sym]->destroy();
      _def[sym]=0;
    }
  }

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

}
