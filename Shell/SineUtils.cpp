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
 * @file SineUtils.cpp
 * Implements class SineUtils.
 */

#include <cmath>
#include <climits>

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
#include "Kernel/Problem.hpp"
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

/**
 * Return @b SymId that is greater than any @b SymId that can come from
 * the current problem
 *
 * The returned value is to be used to determine the size of various
 * arrays.
 */
SineSymbolExtractor::SymId SineSymbolExtractor::getSymIdBound()
{
  return max(env.signature->predicates()*3-1, 
         max(env.signature->functions()*3, env.signature->typeCons()*3));
}

void SineSymbolExtractor::addSymIds(Term* term, Stack<SymId>& ids)
{
  CALL("SineSymbolExtractor::addSymIds");

  if (!term->shared()) {
    if (term->isSpecial()) {
      Term::SpecialTermData *sd = term->getSpecialData();
      switch (sd->getType()) {
        case Term::SF_FORMULA:
          extractFormulaSymbols(sd->getFormula(), ids);
              break;
        case Term::SF_ITE:
          extractFormulaSymbols(sd->getCondition(), ids);
              break;
        case Term::SF_LET:
        case Term::SF_LET_TUPLE: {
          TermList binding = sd->getBinding();
          if (binding.isTerm()) {
            addSymIds(binding.term(), ids);
          }
          break;
        }
        case Term::SF_TUPLE: {
          addSymIds(sd->getTupleTerm(), ids);
          break;
        }
        case Term::SF_MATCH: {
          // args are handled below
          break;
        }
        default:
          ASSERTION_VIOLATION;
      }
    } else {
      //all sorts should be shared
      ids.push(term->functor() * 3 + 1);
    }
    NonVariableIterator nvi(term);
    while (nvi.hasNext()) {
      addSymIds(nvi.next().term(), ids);
    }
  } else {
    if(term->isSort()){
      ids.push(term->functor() * 3 + 2);
    } else {
      ids.push(term->functor() * 3 + 1);
    }

    NonVariableIterator nvi(term);
    while (nvi.hasNext()) {
      Term* t = nvi.next().term();
      if(t->isSort()){
        ids.push(t->functor() * 3 + 2);
      } else {
        ids.push(t->functor() * 3 + 1);
      }
    }
  }
}

/**
 * Add all occurrences of symbol ids of symbols occurring in the the literal to @c ids.
 * @since 04/05/2013 Manchester, argument polarity removed
 * @author Andrei Voronkov
 */
void SineSymbolExtractor::addSymIds(Literal* lit,Stack<SymId>& ids)
{
  CALL("SineSymbolExtractor::addSymIds");

  SymId predId=lit->functor()*3;
  ids.push(predId);

  if (!lit->shared()) {
    NonVariableIterator nvi(lit);
    while (nvi.hasNext()) {
      addSymIds(nvi.next().term(), ids);
    }
  } else {
    NonVariableIterator nvi(lit);
    while (nvi.hasNext()) {
      Term *t = nvi.next().term();
      if(t->isSort()){
        ids.push(t->functor() * 3 + 2);
      } else {
        ids.push(t->functor() * 3 + 1);
      }      
    }
  }
} // addSymIds

void SineSymbolExtractor::decodeSymId(SymId s, bool& pred, unsigned& functor)
{
  pred = (s%2)==0;
  functor = s/2;
}

bool SineSymbolExtractor::validSymId(SymId s)
{
  CALL("SineSymbolExtractor::validSymId");

  bool pred;
  unsigned functor;
  decodeSymId(s, pred, functor);
  if (pred) {
    if (functor>=static_cast<unsigned>(env.signature->predicates())) {
      return false;
    }
  }
  else {
    if (functor>=static_cast<unsigned>(env.signature->functions())) {
      return false;
    }
  }
  return true;
}

/**
 * Add all occurrences of symbol ids of symbols occurring in the formula to @c ids.
 * @since 04/05/2013 Manchester, argument polarity removed, made non-recursive
 * @author Andrei Voronkov
 */
void SineSymbolExtractor::extractFormulaSymbols(Formula* f,Stack<SymId>& itms)
{
  CALL("SineSymbolExtractor::extractFormulaSymbols");
  Stack<Formula*> fs;
  fs.push(f);
  while (!fs.isEmpty()) {
    Formula* f = fs.pop();
    switch (f->connective()) {
    case LITERAL:
      addSymIds(f->literal(),itms);
      break;
    case BOOL_TERM: {
      TermList ts = f->getBooleanTerm();
      if (ts.isTerm()) {
        addSymIds(ts.term(), itms);
      }
      break;
    }
    case AND:
    case OR:
      {
	FormulaList::Iterator args(f->args());
	while (args.hasNext()) {
	  fs.push(args.next());
	}
      }
      break;
    case IMP:
    case IFF:
    case XOR:
      fs.push(f->left());
      fs.push(f->right());
      break;
    case NOT:
      fs.push(f->uarg());
      break;
    case FORALL:
    case EXISTS:
      fs.push(f->qarg());
      break;
    case TRUE:
    case FALSE:
      break;
    case NAME:
    case NOCONN:
      ASSERTION_VIOLATION;
    }
  }
} // SineSymbolExtractor::extractFormulaSymbols

/**
 * Return iterator that yields SymIds of symbols in a unit.
 * Each SymId is yielded at most once.
 */
SineSymbolExtractor::SymIdIterator SineSymbolExtractor::extractSymIds(Unit* u)
{
  CALL("SineSymbolExtractor::extractSymIds");

  static Stack<SymId> itms;
  itms.reset();

  if (u->isClause()) {
    Clause* cl=static_cast<Clause*>(u);
    unsigned clen=cl->length();
    for (unsigned i=0;i<clen;i++) {
      Literal* lit=(*cl)[i];
      addSymIds(lit,itms);
    }
  } else {
    FormulaUnit* fu=static_cast<FormulaUnit*>(u);
    extractFormulaSymbols(fu->formula(),itms);
  }
  return pvi( getUniquePersistentIterator(Stack<SymId>::Iterator(itms)) );
}

void SineBase::initGeneralityFunction(UnitList* units)
{
  CALL("SineBase::initGeneralityFunction");

  SymId symIdBound=_symExtr.getSymIdBound();
  _gen.init(symIdBound,0);

  UnitList::Iterator uit(units);
  while (uit.hasNext()) {
    Unit* u=uit.next();
    SymIdIterator sit=_symExtr.extractSymIds(u);
    while (sit.hasNext()) {
      SymId sid=sit.next();
      _gen[sid]++;
    }
  }
}

SineSelector::SineSelector(const Options& opt)
: _onIncluded(opt.sineSelection()==Options::SineSelection::INCLUDED),
  _genThreshold(opt.sineGeneralityThreshold()),
  _tolerance(opt.sineTolerance()),
  _depthLimit(opt.sineDepth()),
  _justForSineLevels(false)
{
  CALL("SineSelector::SineSelector/0");

  init();
}

SineSelector::SineSelector(bool onIncluded, float tolerance, unsigned depthLimit, unsigned genThreshold, bool justForSineLevels)
: _onIncluded(onIncluded),
  _genThreshold(genThreshold),
  _tolerance(tolerance),
  _depthLimit(depthLimit),
  _justForSineLevels(justForSineLevels)
{
  CALL("SineSelector::SineSelector/4");

  init();
}

void SineSelector::init()
{
  CALL("SineSelector::init");
  ASS(_tolerance>=1.0f || _tolerance==-1);

  _strict=_tolerance==1.0f;
}

/**
 * Connect unit @b u with symbols it defines
 */
void SineSelector::updateDefRelation(Unit* u)
{
  CALL("SineSelector::updateDefRelation");

  SymIdIterator sit=_symExtr.extractSymIds(u);

  if (!sit.hasNext()) {
    if(_justForSineLevels){
      u->inference().setSineLevel(0);
      //cout << "set level for a non-symboler " << u->toString() << " as " << "(0)" << endl;
    }
    _unitsWithoutSymbols.push(u);
    return;
  }

  static Stack<SymId> equalGenerality;
  equalGenerality.reset();

  SymId leastGenSym=sit.next();
  unsigned leastGenVal=_gen[leastGenSym];

  //it a symbol fits under _genThreshold, add it immediately [into the relation]
  if (leastGenVal<=_genThreshold) {
    UnitList::push(u,_def[leastGenSym]);
  }

  while (sit.hasNext()) {
    SymId sym=sit.next();
    unsigned val=_gen[sym];
    ASS_G(val,0);

    //it a symbol fits under _genThreshold, add it immediately [into the relation]
    if (val<=_genThreshold) {
      UnitList::push(u,_def[sym]);
    }

    if (val<leastGenVal) {
      leastGenSym=sym;
      leastGenVal=val;
      equalGenerality.reset();
    } else if (val==leastGenVal) {
      equalGenerality.push(sym);
    }
  }


  if (_strict) {
    //only if the least general symbol is over _genThreshold; otherwise it is already added
    if (leastGenVal>_genThreshold) {
      UnitList::push(u,_def[leastGenSym]);
      while (equalGenerality.isNonEmpty()) {
        UnitList::push(u,_def[equalGenerality.pop()]);
      }
    }
  }
  else {
    unsigned generalityLimit=static_cast<int>(leastGenVal*_tolerance);
    if (_tolerance==-1.0f) {
      generalityLimit = UINT_MAX;
    }

    //if the generalityLimit is under _genThreshold, all suitable symbols are already added
    if (generalityLimit>_genThreshold) {
      sit=_symExtr.extractSymIds(u);
      while (sit.hasNext()) {
	SymId sym=sit.next();
	unsigned val=_gen[sym];
	//only if the symbol is over _genThreshold; otherwise it is already added
	if (val>_genThreshold && val<=generalityLimit) {
	  UnitList::push(u,_def[sym]);
	}
      }
    }
  }

}

void SineSelector::perform(Problem& prb)
{
  CALL("SineSelector::perform");

  if (perform(prb.units())) {
    prb.reportIncompleteTransformation();
  }
  prb.invalidateByRemoval();
}

bool SineSelector::perform(UnitList*& units)
{
  CALL("SineSelector::perform");

  TimeCounter tc(TC_SINE_SELECTION);

  initGeneralityFunction(units);

  SymId symIdBound=_symExtr.getSymIdBound();

  Set<Unit*> selected;
  Stack<Unit*> selectedStack; //on this stack there are Units in the order they were selected
  Deque<Unit*> newlySelected;

  //build the D-relation and select the non-axiom formulas
  _def.init(symIdBound,0);
  unsigned numberUnitsLeftOut = 0;
  UnitList::Iterator uit2(units);
  while (uit2.hasNext()) {
    numberUnitsLeftOut++;
    Unit* u=uit2.next();
    bool performSelection= _onIncluded ? u->included() : ((u->inputType()==UnitInputType::AXIOM)
                            || (env.options->guessTheGoal() != Options::GoalGuess::OFF && u->inputType()==UnitInputType::ASSUMPTION));
    if (performSelection) { // register the unit for later
      updateDefRelation(u);
    }
    else { // goal units are immediately taken (well, non-axiom, to by more precise. Includes ASSUMPTION, which cl->isGoal() does not take into account)
      selected.insert(u);
      selectedStack.push(u);
      newlySelected.push_back(u);

      if(_justForSineLevels) {
        u->inference().setSineLevel(0);
        //cout << "set level for " << u->toString() << " as " << "(0)" << endl;
      }
    }
  }

  unsigned depth=0;
  newlySelected.push_back(0);

  // cout << "env.maxClausePriority starts as" << env.maxClausePriority << endl;

  //select required axiom formulas
  while (newlySelected.isNonEmpty()) {
    Unit* u=newlySelected.pop_front();

    if (!u) {
      //next selected formulas will be one step further from the original formulas
      depth++;
      
      if (_depthLimit && depth==_depthLimit) {
	break;
      }
      ASS(!_depthLimit || depth<_depthLimit);
      if(_justForSineLevels){
        if (env.maxSineLevel < std::numeric_limits<decltype(env.maxSineLevel)>::max()) { // saturate at 255 or something
          env.maxSineLevel++;
        }
      }
      // cout << "Time to inc" << endl;

      if (newlySelected.isNonEmpty()) {
	//we must push another mark if we're not done yet
	newlySelected.push_back(0);
      }
      continue;
    }

    SymIdIterator sit=_symExtr.extractSymIds(u);
    while (sit.hasNext()) {
      SymId sym=sit.next();

      if (env.predicateSineLevels) {
        bool pred;
        unsigned functor;
        SineSymbolExtractor::decodeSymId(sym,pred,functor);
        if (pred && !env.predicateSineLevels->find(functor)) {
          env.predicateSineLevels->insert(functor,env.maxSineLevel);
          // cout << "set level of predicate " << functor << " i.e. " << env.signature->predicateName(functor) << " to " << env.maxClausePriority << endl;
        }
      }

      UnitList::Iterator defUnits(_def[sym]);
      while (defUnits.hasNext()) {
        Unit* du=defUnits.next();
        if (selected.contains(du)) {
          continue;
        }
        selected.insert(du);
        selectedStack.push(du);
        newlySelected.push_back(du);

        if(_justForSineLevels){
          du->inference().setSineLevel(env.maxSineLevel);
          //cout << "set level for " << du->toString() << " in iteration as " << env.maxClausePriority << endl;
        }
      }
      //all defining units for the symbol sym were selected,
      //so we can remove them from the relation
      UnitList::destroy(_def[sym]);
      _def[sym]=0;
    }
  }

  if (_justForSineLevels) {
    // units we did not touch will by default keep their sineLevel == UINT_MAX
    return false;
  }

  env.statistics->sineIterations=depth;
  env.statistics->selectedBySine=_unitsWithoutSymbols.size() + selectedStack.size();

  numberUnitsLeftOut -= env.statistics->selectedBySine;

  UnitList::destroy(units);
  units=0;
  UnitList::pushFromIterator(Stack<Unit*>::Iterator(_unitsWithoutSymbols), units);
  while (selectedStack.isNonEmpty()) {
    UnitList::push(selectedStack.pop(), units);
  }

#if SINE_PRINT_SELECTED
  UnitList::Iterator selIt(units);
  while (selIt.hasNext()) {
    cout<<'#'<<selIt.next()->toString()<<endl;
  }
#endif

  return (numberUnitsLeftOut > 0);
}

//////////////////////////////////////
// SineTheorySelector
//////////////////////////////////////

SineTheorySelector::SineTheorySelector(const Options& opt)
: _genThreshold(opt.sineGeneralityThreshold()), _opt(opt)
{
  CALL("SineTheorySelector::SineTheorySelector");
}

void SineTheorySelector::handlePossibleSignatureChange()
{
  CALL("SineTheorySelector::handlePossibleSignatureChange");

  size_t symIdBound=_symExtr.getSymIdBound();
  size_t oldSize=_def.size();
  ASS_EQ(_gen.size(), oldSize);

  if (symIdBound==oldSize) {
    return;
  }
  ASS_G(symIdBound, oldSize);

  _gen.expand(symIdBound);
  _def.expand(symIdBound);
  for (size_t i=oldSize;i<symIdBound;i++) {
    _gen[i]=0;
    _def[i]=0;
  }
}

/**
 * Connect unit @b u with symbols it defines
 */
void SineTheorySelector::updateDefRelation(Unit* u)
{
  CALL("SineTheorySelector::updateDefRelation");

  SymIdIterator sit0=_symExtr.extractSymIds(u);

  if (!sit0.hasNext()) {

    _unitsWithoutSymbols.push(u);
    return;
  }

  static Stack<SymId> symIds;
  symIds.reset();
  symIds.loadFromIterator(sit0);

  Stack<SymId>::Iterator sit(symIds);

  ALWAYS(sit.hasNext());
  unsigned leastGenVal=_gen[sit.next()];

  while (sit.hasNext()) {
    SymId sym=sit.next();
    unsigned val=_gen[sym];
    ASS_G(val,0);

    if (val<leastGenVal) {
      leastGenVal=val;
    }
  }

  unsigned generalityLimit=leastGenVal*(maxTolerance/strictTolerance);

  Stack<SymId>::Iterator sit2(symIds);
  while (sit2.hasNext()) {
    SymId sym=sit2.next();
    unsigned val=_gen[sym];

    if (val<=_genThreshold) {
      //if a symbol fits under _genThreshold, add it into the relation
      DEntryList::push(DEntry(strictTolerance,u),_def[sym]);
    }
    else if (val<=generalityLimit) {
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

  //build the D-relation
  _def.init(symIdBound,0);
  UnitList::Iterator uit(units);
  while (uit.hasNext()) {
    Unit* u=uit.next();
    updateDefRelation(u);
  }
}


void SineTheorySelector::perform(UnitList*& units)
{
  CALL("SineTheorySelector::perform");

  TimeCounter tc(TC_SINE_SELECTION);

  handlePossibleSignatureChange();

  UnitList::Iterator uit(units);
  while (uit.hasNext()) {
    Unit* u=uit.next();
    SymIdIterator sit=_symExtr.extractSymIds(u);
    while (sit.hasNext()) {
      SymId sid=sit.next();
      _gen[sid]++;
    }
  }

  UnitList* res=0;
  DHSet<SymId> addedSymIds;
  DHSet<Unit*> selected;
  Deque<Unit*> newlySelected;

  bool sineOnIncluded=_opt.sineSelection()==Options::SineSelection::INCLUDED;

  //build the D-relation and select the non-axiom formulas
  UnitList::Iterator uit2(units);
  while (uit2.hasNext()) {
    Unit* u=uit2.next();
    bool performSelection= sineOnIncluded ? u->included() : ((u->inputType()==UnitInputType::AXIOM)
                   || (env.options->guessTheGoal() != Options::GoalGuess::OFF && u->inputType()==UnitInputType::ASSUMPTION));

    if (performSelection) {
      updateDefRelation(u);
    }
    else {
      selected.insert(u);
      newlySelected.push_back(u);
      UnitList::push(u,res);
    }
  }


  unsigned short intTolerance=static_cast<unsigned short>(ceil(_opt.sineTolerance()*10));

  unsigned depthLimit=_opt.sineDepth();
  unsigned depth=0;
  newlySelected.push_back(0);

  //select required axiom formulas
  while (newlySelected.isNonEmpty()) {
    Unit* u=newlySelected.pop_front();

    if (!u) {
      //next selected formulas will be one step further from the original formulas
      depth++;
      if (depthLimit && depth==depthLimit) {
	break;
      }
      ASS(!depthLimit || depth<depthLimit);

      if (newlySelected.isNonEmpty()) {
	//we must push another mark if we're not done yet
	newlySelected.push_back(0);
      }
      continue;
    }

    SymIdIterator sit=_symExtr.extractSymIds(u);
    while (sit.hasNext()) {
      SymId sym=sit.next();
      if (!addedSymIds.insert(sym)) {
	//we already added units belonging to this symbol
	continue;
      }
      DEntryList::Iterator defUnits(_def[sym]);
      while (defUnits.hasNext()) {
	DEntry de=defUnits.next();

	if (de.minTolerance>intTolerance || !selected.insert(de.unit)) {
	  continue;
	}
	UnitList::push(de.unit,res);
	newlySelected.push_back(de.unit);
      }
    }
  }

  UnitList::pushFromIterator(Stack<Unit*>::Iterator(_unitsWithoutSymbols), res);

  UnitList::destroy(units);
//  units=res->reverse(); //we want to resemble the original SInE as much as possible
  units=res;

  env.statistics->sineIterations=depth;
  env.statistics->selectedBySine=_unitsWithoutSymbols.size() + selected.size();

#if SINE_PRINT_SELECTED
  UnitList::Iterator selIt(units);
  while (selIt.hasNext()) {
    cout<<'#'<<selIt.next()->toString()<<endl;
  }
#endif
}

}
