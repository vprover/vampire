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
 * @file PredicateDefinition.hpp
 * Defines class PredicateDefinition.
 */


#ifndef __PredicateDefinition__
#define __PredicateDefinition__

#include "Forwards.hpp"

#include "Lib/DArray.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/VirtualIterator.hpp"
#include "Kernel/FormulaUnit.hpp"

#include "SymCounter.hpp"

namespace Shell {

using namespace Lib;
using namespace Kernel;

/**
 * Performs removal (and simplification) of unused predicate definitions
 * and removal of pure predicates.
 *
 * Definition removal:
 *
 * Definition is a formula forall X: p(X) <=> F[X]
 */
class PredicateDefinition
{
public:
  typedef DHMap<Unit*, Unit*> ReplMap;

  PredicateDefinition();
  ~PredicateDefinition();

  void collectReplacements(UnitList* units, ReplMap& unitReplacements);

  void removeUnusedDefinitionsAndPurePredicates(Problem& prb);
  void removeUnusedDefinitionsAndPurePredicates(UnitList*& units);

  void addBuiltInPredicate(unsigned pred);
private:
  struct Def;
  struct PredData;

  void scan(Unit* u);
  void scan(Clause* u);
  void scan(FormulaUnit* u);
  void count (TermList ts,int add, Unit* unit);
  void count (Formula* f,int polarity,int add, Unit* unit);
  void count (FormulaUnit* f,int add) { count(f->formula(), 1, add, f); }
  void count (Clause* cl,int add);
  void count (Unit* u,int add);
  bool tryGetDef(Literal* lhs, Formula* rhs, FormulaUnit* unit);

  FormulaUnit* replacePurePredicates(FormulaUnit* u);
  Formula* replacePurePredicates(Formula* u);
  Clause* replacePurePredicates(Clause* u);
  Unit* replacePurePredicates(Unit* u);

  FormulaUnit* makeImplFromDef(FormulaUnit* def, unsigned pred, bool forward);

  Unit* getReplacement(Unit* u, ReplMap& replacements);
  FormulaUnit* getReplacement(FormulaUnit* u, ReplMap& replacements);

  void eliminatePredicateDefinition(unsigned pred, ReplMap& replacements);
  void replacePurePred(unsigned pred, ReplMap& replacements);
  
  Problem* _processedPrb;

  unsigned _predCnt;
  PredData* _preds;

  DHMap<unsigned, Def*> _defs;
  DHMap<unsigned, bool> _purePreds;
  Stack<int> _eliminable;
  Stack<int> _pureToReplace;
};

};

#endif /* __PredicateDefinition__ */
