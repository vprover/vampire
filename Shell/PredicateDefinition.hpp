/**
 * @file PredicateDefinition.hpp
 * Defines class PredicateDefinition.
 */


#ifndef __PredicateDefinition__
#define __PredicateDefinition__

#include "Forwards.hpp"

#include "Lib/DArray.hpp"
#include "Lib/DHMap.hpp"
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
 * Definition is a formula \forall \vec{X}: p(\vec{X}) <=> F[\vec{X}]
 */
class PredicateDefinition
{
public:
  PredicateDefinition();
  ~PredicateDefinition();

  void collectReplacements(UnitList* units, DHMap<Unit*, Unit*>& unitReplacements);

  void removeUnusedDefinitionsAndPurePredicates(UnitList*& units);

  void addBuiltInPredicate(unsigned pred);

  static bool isBuiltIn(unsigned pred);

private:
  struct Def;
  struct PredData;

  void scan(Unit* u);
  void scan(Clause* u);
  void scan(FormulaUnit* u);
  void count (Formula* f,int polarity,int add, Unit* unit);
  void count (FormulaUnit* f,int add) { count(f->formula(), 1, add, f); }
  void count (Clause* f,int add);
  bool tryGetDef(Literal* lhs, Formula* rhs, FormulaUnit* unit);

  FormulaUnit* replacePurePredicates(FormulaUnit* u);
  Formula* replacePurePredicates(Formula* u);
  Clause* replacePurePredicates(Clause* u);
  Unit* replacePurePredicates(Unit* u);

  void makeImplFromDef(unsigned pred, bool forward);

  int _predCnt;
  PredData* _preds;

  DHMap<unsigned, Def*> _defs;
  DHMap<unsigned, bool> _purePreds;
  Stack<int> _eliminable;
  Stack<int> _pureToReplace;
};

};

#endif /* __PredicateDefinition__ */
