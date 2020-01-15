
/*
 * File Selector.cpp.
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
 * @file Selector.cpp
 * Implements class Selector.
 */

#include "Lib/DHMap.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Exception.hpp"
#include "Lib/Stack.hpp"
#include "Lib/TimeCounter.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "Selector.hpp"

namespace Shell
{
namespace LTB
{

using namespace Lib;
using namespace Kernel;

class SignatureMap
{
public:
  SignatureMap(Storage* storage)
  : _storage(storage)
  {
  }
private:
  Storage* _storage;

  DHMap<unsigned,unsigned> _predLoc2Glob;
  DHMap<unsigned,unsigned> _funLoc2Glob;
  DHMap<unsigned,unsigned> _predGlob2Loc;
  DHMap<unsigned,unsigned> _funGlob2Loc;
};

/**
 * Class for obtaining global SymIds from units.
 *
 * Global SymIds correspond to the signature used in the theory stored
 * in the @b Storage object passed to the constructor.
 */
class TranslatingSymbolCollector
{
public:
  TranslatingSymbolCollector(Storage* storage)
  : _storage(storage)
  {
  }

  void collectSymIds(Unit* u);

  SymIdIterator getSymIds();

private:
  DHSet<SymId> _collected;

  SineSymbolExtractor _sSymExtr;
  Storage* _storage;
};


void TranslatingSymbolCollector::collectSymIds(Unit* u)
{
  CALL("TranslatingSymbolCollector::collectSymIds");

  SymIdIterator locSymIds=_sSymExtr.extractSymIds(u);
  while(locSymIds.hasNext()) {
    SymId s=locSymIds.next();
    _collected.insert(s);
  }
}

/**
 * Return collected global SymIds
 *
 * Local SymIds that don't have a global counterpart are discarded.
 */
SymIdIterator TranslatingSymbolCollector::getSymIds()
{
  CALL("TranslatingSymbolExtractor::extractSymIds");

//  static Stack<SymId> unknownSymIds;
//  unknownSymIds.reset();
//
//  while(locSymIds.hasNext()) {
//    SymId s=locSymIds.next();
//    SymId gs;
//    if(_dict.find(s, gs)) {
//      List<SymId>::push(gs, res);
//    }
//    else {
//      unknownSymIds.push(s);
//    }
//  }

  Stack<pair<bool, unsigned> > queries;
  SymIdIterator sit=_collected.iterator();
  while(sit.hasNext()) {
    SymId s=sit.next();
    bool pred;
    unsigned functor;
    _sSymExtr.decodeSymId(s, pred, functor);
    queries.push(make_pair(pred, functor));
  }


  int globPreds;
  int globFuns;
  _storage->getSignatureSize(globPreds, globFuns);

  VirtualIterator<pair<bool, unsigned> > results=_storage->getGlobalSymbols(queries);
  List<SymId>* res=0;

  while(results.hasNext()) {
    pair<bool, unsigned> s=results.next();
    SymId sid;
    if(s.first) {
      sid=s.second;
    }
    else {
      sid=globPreds+s.second;
    }
    List<SymId>::push(sid, res);
  }

  return pvi( List<SymId>::DestructiveIterator(res) );
}


void Selector::selectForProblem(UnitList*& units)
{
  CALL("Selector::selectForProblem");

  TimeCounter tc(TC_SINE_SELECTION);

  if(_storage.getEmptyClausePossession()) {
    Clause* cl=Clause::fromIterator(VirtualIterator<Literal*>::getEmpty(), Unit::AXIOM, new Inference0(Inference::EXTERNAL_THEORY_AXIOM));
    units->destroy();
    units=0;
    UnitList::push(cl, units);
    return;
  }

  TranslatingSymbolCollector tsc(&_storage);
  UnitList::Iterator uit(units);
  while(uit.hasNext()) {
    tsc.collectSymIds(uit.next());
  }

  unsigned itolerance=static_cast<unsigned>(100*env.options->sineTolerance());

  DHSet<SymId> selectedSymbols;
  Stack<SymId> newlySelected;

  newlySelected.loadFromIterator(tsc.getSymIds());
  selectedSymbols.loadFromIterator(Stack<SymId>::Iterator(newlySelected));

  unsigned depthLimit=env.options->sineDepth();
  unsigned depth=1;
  for(;;) {
    if(depthLimit && depth==depthLimit) {
      break;
    }

    SymIdIterator sit=_storage.getDRelatedSymbols(newlySelected, itolerance);
    newlySelected.reset();
    while(sit.hasNext()) {
      SymId s=sit.next();
      if(selectedSymbols.insert(s)) {
	newlySelected.push(s);
      }
    }
    if(newlySelected.isEmpty()) {
      break;
    }
    depth++;
  }

  env.statistics->sineIterations=depth;

  DHSet<unsigned> selectedFormulas;
  selectedFormulas.loadFromIterator(_storage.getNumbersOfUnitsWithoutSymbols());
  selectedFormulas.loadFromIterator(_storage.getDRelatedUnitNumbers(selectedSymbols.iterator(), itolerance));

  UnitList* selected=_storage.getClausesByUnitNumbers(selectedFormulas.iterator());

  units=UnitList::concat(units, selected);
}


}
}

