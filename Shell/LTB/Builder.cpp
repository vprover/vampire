/**
 * @file Builder.cpp
 * Implements class Builder.
 */

#include <fstream>

#include "Lib/DHSet.hpp"
#include "Lib/Environment.hpp"
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
#include "Shell/TPTPLexer.hpp"
#include "Shell/TPTPParser.hpp"

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
  static Comparison compare(const string& a, const string& b)
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


void Builder::build(VirtualIterator<string> fnameIterator)
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
    string fname=fnit.next();
    ifstream input(fname.c_str());

    TPTPLexer lexer(input);
    TPTPParser parser(lexer);
    UnitList* newUnits = parser.units();

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
  clausifyOptions._theoryAxioms=false;
  clausifyOptions._unusedPredicateDefinitionRemoval=false;
  clausifyOptions._functionDefinitionElimination=Options::FDE_NONE;
  clausifyOptions._inequalitySplitting=0;
  clausifyOptions._equalityResolutionWithDeletion=Options::RA_OFF;
  clausifyOptions._equalityProxy=Options::EP_OFF;
  clausifyOptions._generalSplitting=Options::RA_OFF;

  //and now to the storing part
  UnitList::Iterator uit(units);
  while(uit.hasNext()) {
    Unit* u=uit.next();

    UnitList* localUnits=0;
    UnitList::push(u, localUnits);

    Property prop;
    prop.scan(localUnits);
    Preprocess preproc(prop, clausifyOptions);
    preproc.preprocess(localUnits);

    ClauseIterator cit=pvi( getStaticCastIterator<Clause*>(UnitList::Iterator(localUnits)) );
    storage.storeCNFOfUnit(u->number(), cit);
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
  Stack<DSymRecord> symStack;
  Stack<DSymRecord> symUniqueStack;
  for(SymId i=0;i<symIdBound;i++) {

    unitStack.reset();
    symStack.reset();
    symUniqueStack.reset();

    while(_def[i]) {
      DUnitRecord dur;
      dur=DURList::pop(_def[i]);

      unitStack.push(dur);

      SymIdIterator sit2=_symExtr.extractSymIds(dur.second);
      ASS(sit2.hasNext());
      while(sit2.hasNext()) {
        symStack.push(make_pair(dur.first, sit2.next()));
      }
    }

    sort<DRecordComparator>(unitStack.begin(), unitStack.end());
    sort<DRecordComparator>(symStack.begin(), symStack.end());


    //tolerance thresholds are at lest 100, so nothing will be equal to the initial value
    DSymRecord prevDSR=make_pair(0,0);
    Stack<DSymRecord>::Iterator ssit(symStack);
    while(ssit.hasNext()) {
      DSymRecord dsr=ssit.next();
      if(prevDSR==dsr) {
	continue;
      }
      symUniqueStack.push(dsr);
      prevDSR=dsr;
    }
    storage.storeDURs(i, unitStack);
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

