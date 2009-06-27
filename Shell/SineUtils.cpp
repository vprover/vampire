/**
 * @file SineUtils.cpp
 * Implements class SineUtils.
 */

#include "../Lib/DHMultiset.hpp"
#include "../Lib/MapToLIFO.hpp"
#include "../Lib/Metaiterators.hpp"
#include "../Lib/Set.hpp"
#include "../Lib/VirtualIterator.hpp"

#include "../Kernel/Clause.hpp"
#include "../Kernel/FormulaUnit.hpp"
#include "../Kernel/SubformulaIterator.hpp"
#include "../Kernel/Term.hpp"
#include "../Kernel/TermFunIterator.hpp"

#include "SineUtils.hpp"

#define SINE_PRINT_SELECTED 0

namespace Shell
{
namespace SineAux
{

using namespace Lib;
using namespace Kernel;

typedef int SymId;
typedef VirtualIterator<SymId> SymIdIterator;

SymId getSymId(Literal* lit, bool polarity)
{
//  return lit->functor()*2 + (polarity^lit->isNegative()?0:1);
  return lit->functor();
}
SymId getSymId(Term* t)
{
  ASS(!t->isLiteral());
  return -(t->functor()+1);
}
SymId getDefiningSymId(SymId sid)
{
//  if(sid>=0) {
//    return sid^1;
//  }
  return sid;
}

struct IsLiteralFormulaFn
{
  DECL_RETURN_TYPE(bool);
  bool operator()(Formula* f)
  {
    return f->connective()==LITERAL;
  }
};

struct FunctionSymIdFn
{
  DECL_RETURN_TYPE(SymId);
  SymId operator()(TermList t)
  {
    ASS(t.isTerm());
    return getSymId(t.term());
  }
};

struct LiteralSymIdsFn
{
  DECL_RETURN_TYPE(SymIdIterator);
  SymIdIterator operator()(Formula* f)
  {
    ASS_EQ(f->connective(),LITERAL);
    return (*this)(f->literal());
  }
  SymIdIterator operator()(Literal* lit)
  {
    return pvi( getConcatenatedIterator(
	    getSingletonIterator( getSymId(lit) ),
	    getMappingIterator(
		    vi( new Term::NonVariableIterator(lit) ),
		    FunctionSymIdFn() )
	    ) );
  }
};


void addFormulaSymbols(Formula* f,int polarity,Stack<SymId>& itms)
{
  CALL("PredicateDefinition::addFormulaSymbols");

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
		    FunctionSymIdFn()) );
      return;
    }

    case AND:
    case OR: {
      FormulaList::Iterator fs(f->args());
      while (fs.hasNext()) {
	addFormulaSymbols (fs.next(),polarity,itms);
      }
      return;
    }

    case IMP:
      addFormulaSymbols (f->left(), -polarity, itms);
      addFormulaSymbols (f->right(), polarity, itms);
      return;

    case NOT:
      addFormulaSymbols (f->uarg(), -polarity, itms);
      return;

    case IFF:
    case XOR:
      addFormulaSymbols (f->left(), 0, itms);
      addFormulaSymbols (f->right(), 0, itms);
      return;

    case FORALL:
    case EXISTS:
      addFormulaSymbols (f->qarg(), polarity, itms);
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
SymIdIterator getSymIds(Unit* u)
{
  Stack<SymId> itms;
  if(u->isClause()) {
    Clause* cl=static_cast<Clause*>(u);
    unsigned clen=cl->length();
    for(unsigned i=0;i<clen;i++) {
      Literal* lit=(*cl)[i];
      itms.push( getSymId(lit, true) );
      itms.pushFromIterator( getMappingIterator(
		    vi( new Term::NonVariableIterator(lit) ),
		    FunctionSymIdFn()) );
    }
  } else {
    FormulaUnit* fu=static_cast<FormulaUnit*>(u);
    addFormulaSymbols(fu->formula(), 1, itms);
  }
  return pvi( getUniquePersistentIterator(Stack<SymId>::Iterator(itms)) );
}

class GeneralityMeasure
{
public:
  GeneralityMeasure(UnitList* units)
  {
    CALL("GeneralityMeasure::GeneralityMeasure");

    UnitList::Iterator uit(units);
    while(uit.hasNext()) {
      count(uit.next());
    }
  }

  int generality(SymId sid)
  {
    return _appearanceCounter.multiplicity(sid);
  }
private:
  void count(Unit* u)
  {
    CALL("GeneralityMeasure::count(Unit*)");

    Set<SymId> symbols;

    SymIdIterator sit=getSymIds(u);
    while(sit.hasNext()) {
      SymId sid=sit.next();
      _appearanceCounter.insert(sid);
    }
  }

  DHMultiset<SymId, IdentityHash> _appearanceCounter;
};

class DefRelation
{
public:
  DefRelation(UnitList* units)
  {
    GeneralityMeasure gm(units);
    Stack<SymId> equalGenerality;

    UnitList::Iterator uit(units);
    while(uit.hasNext()) {
      Unit* u=uit.next();

      if(u->inputType()!=Unit::AXIOM) {
        continue;
      }

      SymIdIterator sit=getSymIds(u);

      if(!sit.hasNext()) {
	_unitsWithoutSymbols.push(u);
	continue;
      }
      SymId leastGenSym=sit.next();
      int leastGenVal=gm.generality(leastGenSym);
      int genSum=0;
      int symCnt=1;
      ASS(equalGenerality.isEmpty());

      while(sit.hasNext()) {
	SymId sym=sit.next();
	int val=gm.generality(sym);
	genSum+=val;
	symCnt++;
	if(val<leastGenVal) {
	  leastGenSym=sym;
	  leastGenVal=val;
	  equalGenerality.reset();
	} else if(val==leastGenVal) {
	  equalGenerality.push(sym);
	}
      }

#if 0
//      int avgGen=genSum/symCnt;
      equalGenerality.reset();
//      int treshold=static_cast<int>(leastGenVal*1.5405f);
      int treshold=static_cast<int>(leastGenVal*1.2f);
//      int treshold=leastGenVal+static_cast<int>(genSum*0.01f/symCnt);
//      int treshold=leastGenVal+static_cast<int>((float(genSum)/symCnt-leastGenVal)*0.018f);
      sit=getSymIds(u);
      while(sit.hasNext()) {
	SymId sym=sit.next();
	if(gm.generality(sym)<=treshold) {
	  _data.pushToKey(sym, u);
	}
      }
#else
      _data.pushToKey(leastGenSym, u);
      while(equalGenerality.isNonEmpty()) {
	_data.pushToKey(equalGenerality.pop(), u);
      }
#endif
    }
  }

  UnitIterator definingUnits(SymId sym)
  {
    return pvi( _data.keyIterator(getDefiningSymId(sym)) );
  }

  UnitIterator unitsWithoutSymbols()
  {
    return pvi( Stack<Unit*>::Iterator(_unitsWithoutSymbols) );
  }
private:
  MapToLIFO<SymId, Unit*> _data;
  Stack<Unit*> _unitsWithoutSymbols;
};

}

using namespace Lib;
using namespace Kernel;
using namespace SineAux;

void SineSelector::perform(UnitList*& units)
{
  DefRelation dr(units);
  Set<Unit*> selected;
  //on this stack there are Units in the order they were selected
  Stack<Unit*> selectedStack;
  Stack<Unit*> newlySelected;

  UnitList::Iterator uit(units);
  while(uit.hasNext()) {
    Unit* u=uit.next();
    if(u->inputType()==Unit::AXIOM) {
      continue;
    }
    selected.insert(u);
    selectedStack.push(u);
    newlySelected.push(u);
  }

  while(newlySelected.isNonEmpty()) {
    Unit* u=newlySelected.pop();
    SymIdIterator sit=getSymIds(u);
    while(sit.hasNext()) {
      SymId sym=sit.next();
      UnitIterator defUnits=dr.definingUnits(sym);
      while(defUnits.hasNext()) {
	Unit* du=defUnits.next();
	if(selected.contains(du)) {
	  continue;
	}
	selected.insert(du);
	selectedStack.push(du);
	newlySelected.push(du);
      }
    }
  }

//  UnitList::Iterator uit2(units);
//  while(uit2.hasNext()) {
//    Unit* u=uit2.next();
//    if(u->inputType()!=Unit::AXIOM) {
//      continue;
//    }
//    if(selected.contains(u)) {
//      u->setInputType(Unit::LEMMA);
//    }
//  }

  units->destroy();
  units=0;
  UnitList::pushFromIterator(dr.unitsWithoutSymbols(), units);
  while(selectedStack.isNonEmpty()) {
    UnitList::push(selectedStack.pop(), units);
  }

#if SINE_PRINT_SELECTED
  UnitList::Iterator selIt(units);
  while(selIt.hasNext()) {
    cout<<selIt.next()->toString()<<endl;
  }
#endif
}

}
