
/*
 * File Builder.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file Builder.cpp
 * Implements class Builder.
 */

#include <fstream>

#include "Lib/DHSet.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/List.hpp"
#include "Lib/Sort.hpp"
#include "Lib/Stack.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"

#include "Shell/Normalisation.hpp"
#include "Shell/Options.hpp"
#include "Shell/Preprocess.hpp"
#include "Shell/Property.hpp"
#include "Shell/SineUtils.hpp"

#include "Parse/TPTP.hpp"

#include "Storage.hpp"
#include "Builder.hpp"

namespace Shell
{
namespace LTB
{

Builder::Builder()
{
  CALL("Builder::Builder");

  _genThreshold=env.options->sineGeneralityThreshold();
}

struct StringComparator
{
  static Comparison compare(const vstring& a, const vstring& b)
  {
    CALL("DefaultComparator::compare");

    int res=a.compare(b);
    if(res==0) {
      return EQUAL;
    }
    else if(res<0) {
      return LESS;
    }
    else {
      ASS(res>0);
      return GREATER;
    }
  }
};

struct DRecordComparator
{
  template<typename T>
  static Comparison compare(const pair<unsigned, T>& a, const pair<unsigned, T>& b)
  {
    CALL("DefaultComparator::compare");

    Comparison res=Int::compare(a.first, b.first);
    if(res==EQUAL) {
      res=DefaultComparator::compare(a.second, b.second);
    }
    return res;
  }
};


void Builder::build(VirtualIterator<vstring> fnameIterator)
{
  CALL("Builder::build");

  StringStack fnames;
  fnames.loadFromIterator(fnameIterator);

  if(env.options->normalize()) {
    sort<StringComparator>(fnames.begin(), fnames.end());
  }

  UnitList* units=0;

  //read units from all the included files
  StringStack::Iterator fnit(fnames);
  while(fnit.hasNext()) {
    vstring fname=fnit.next();
    ifstream input(env.options->includeFileName(fname).c_str());
    if(input.fail()) {
      USER_ERROR("Cannot open included file: "+env.options->includeFileName(fname));
    }
    UnitList* newUnits = Parse::TPTP::parse(input);
    units=UnitList::concat(newUnits, units);
  }

  if(env.options->normalize()) {
    Normalisation norm;
    units=norm.normalise(units);
  }


  Storage storage(false);
  storage.storeTheoryFileNames(fnames);

  //we store CNF of all units

  //first we need to prepare otions for the clausifier
  Options clausifyOptions(*env.options);
  clausifyOptions._normalize=false;
  clausifyOptions._sineSelection=Options::SS_OFF;
  clausifyOptions._unusedPredicateDefinitionRemoval=false;
  clausifyOptions._functionDefinitionElimination=Options::FDE_NONE;
  clausifyOptions._inequalitySplitting=0;
  clausifyOptions._equalityResolutionWithDeletion=Options::RA_OFF;
  clausifyOptions._equalityProxy=Options::EP_OFF;
  clausifyOptions._generalSplitting=Options::RA_OFF;

  bool haveEmptyClause=false;

  //and now to the storing part
  UnitList::Iterator uit(units);
  while(uit.hasNext()) {
    Unit* u=uit.next();

    UnitList* localUnits=0;
    UnitList::push(u, localUnits);

    Property* prop = Property::scan(localUnits);
    Preprocess preproc(*prop,clausifyOptions);
    preproc.preprocess(localUnits);
    delete prop;

    //here we go through generated clauses and we check whether there isn't an empty clause
    //(as storage.storeCNFOfUnit doesn't allow storing them)
    UnitList::Iterator cit0(localUnits);
    while(cit0.hasNext()) {
      Unit* u=cit0.next();
      ASS(u->isClause());
      if(static_cast<Clause*>(u)->isEmpty()) {
	haveEmptyClause=true;
	goto cnf_storing_finished;
      }
    }


    ClauseIterator cit=pvi( getStaticCastIterator<Clause*>(UnitList::Iterator(localUnits)) );
    storage.storeCNFOfUnit(u->number(), cit);
  }

cnf_storing_finished:

  storage.storeEmptyClausePossession(haveEmptyClause);
  if(haveEmptyClause) {
    return;
  }

  storage.storeSignature();



  //from here starts the SInE related part

  _symExtr.onSignatureChange();
  SymId symIdBound=_symExtr.getSymIdBound();

  //determine symbol generality
  _gen.init(symIdBound,0);
  UnitList::DelIterator uit1(units);
  while(uit1.hasNext()) {
    Unit* u=uit1.next();
    SymIdIterator sit=_symExtr.extractSymIds(u);
    if(!sit.hasNext()) {
      uit1.del();
      if(!u->isClause() && static_cast<FormulaUnit*>(u)->formula()->connective()==TRUE) {
	//This is a unit that contains only a true constant, so we can skip it.
	//Such units occurred in the MZR LTB problems.
	continue;
      }
      _unitsWithoutSymbols.push(u);
      continue;
    }
    while(sit.hasNext()) {
      SymId sid=sit.next();
      _gen[sid]++;
    }
  }

  _def.init(symIdBound,0);
  UnitList::DelIterator uit2(units);
  while(uit2.hasNext()) {
    Unit* u=uit2.next();
    updateDefRelation(u);
  }

  _defSyms.init(symIdBound,0);

  Stack<DUnitRecord> unitStack;
  Stack<DUnitRecord> unitUniqueStack;
  DHSet<Unit*> prevUnits;

  Stack<DSymRecord> symStack;
  Stack<DSymRecord> symUniqueStack;
  DHSet<SymId> prevSyms;

  for(SymId i=0;i<symIdBound;i++) {

    unitStack.reset();
    symStack.reset();

    while(_def[i]) {
      DUnitRecord dur;
      dur=DURList::pop(_def[i]);

      unitStack.push(dur);

      SymIdIterator sit2=_symExtr.extractSymIds(dur.second);
      ASS(sit2.hasNext());
      while(sit2.hasNext()) {
	SymId symToAdd=sit2.next();
	if(symToAdd!=i) {
	  symStack.push(make_pair(dur.first, symToAdd));
	}
      }
    }

    sort<DRecordComparator>(unitStack.begin(), unitStack.end());
    sort<DRecordComparator>(symStack.begin(), symStack.end());

    //filter out duplicate symbols
    prevSyms.reset();
    symUniqueStack.reset();
    Stack<DSymRecord>::BottomFirstIterator ssit(symStack);
    while(ssit.hasNext()) {
      DSymRecord dsr=ssit.next();
      if(prevSyms.insert(dsr.second)) {
	symUniqueStack.push(dsr);
      }
    }

    //filter out duplicate units
    prevUnits.reset();
    unitUniqueStack.reset();
    Stack<DUnitRecord>::BottomFirstIterator usit(unitStack);
    while(usit.hasNext()) {
      DUnitRecord dur=usit.next();
      if(prevUnits.insert(dur.second)) {
	unitUniqueStack.push(dur);
      }
    }


    storage.storeDURs(i, unitUniqueStack);
    storage.storeDSRs(i, symUniqueStack);
  }

  storage.storeUnitsWithoutSymbols(_unitsWithoutSymbols);
}

void Builder::updateDefRelation(Unit* u)
{
  CALL("Builder::updateDefRelation");

  SymIdIterator sit=_symExtr.extractSymIds(u);

  static Stack<SymId> symbols;
  symbols.reset();

  unsigned minGen=INT_MAX;
  while(sit.hasNext()) {
    SymId sym=sit.next();
    unsigned val=_gen[sym];
    ASS_G(val,0);

    if(val<=_genThreshold) {
      //it a symbol fits under _genThreshold, add it immediately into the relation
      //with tolerance 1 (i.e. itolerance 100; see @b itoleranceLimit)
      DURList::push(make_pair(100,u),_def[sym]);
    }
    else {
      //otherwise
      symbols.push(sym);
    }

    if(val<minGen) {
      minGen=val;
    }
  }
  //there must have been at leas one symbol as we have handled units without
  //symbols separately
  ASS_L(minGen, INT_MAX);


  Stack<SymId>::Iterator sit2(symbols);
  while(sit2.hasNext()) {
    SymId sym=sit2.next();
    unsigned val=_gen[sym];
    //all symbols fitting under _genThreshold have been handled separately
    ASS_G(val,_genThreshold);

    unsigned itoleranceThreshold=(100*val)/minGen;

    if(itoleranceThreshold<=itoleranceLimit) {
      DURList::push(make_pair(itoleranceThreshold, u),_def[sym]);
    }
  }
}








}
}

