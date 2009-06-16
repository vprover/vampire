/**
 * @file Preprocess.cpp
 * Implements class Preprocess for preprocessing.
 * @since 05/01/2004 Manchester
 * @since 02/06/2007 Manchester, changed to new datastructures
 */

#include "../Debug/Tracer.hpp"

#include "../Kernel/Unit.hpp"
#include "../Kernel/Clause.hpp"

#include "CNF.hpp"
#include "Flattening.hpp"
#include "FunctionDefinition.hpp"
#include "InequalitySplitting.hpp"
#include "Naming.hpp"
#include "Normalisation.hpp"
#include "NNF.hpp"
#include "Options.hpp"
#include "PredicateDefinition.hpp"
#include "Preprocess.hpp"
#include "Property.hpp"
#include "Rectify.hpp"
#include "Skolem.hpp"
#include "SimplifyFalseTrue.hpp"

// #include "../Lib/Sort.hpp"
// #include "ClausalDefinition.hpp"
// #include "Definition.hpp"
// #include "Environment.hpp"
// #include "EqualityProxy.hpp"
// #include "LiteralOrderingFinder.hpp"
// #include "Miniscope.hpp"
// #include "Ordering.hpp"
// #include "RowVariable.hpp"
// #include "TheoryFinder.hpp"
// #include "Problem.hpp"
// #include "PureLiteral.hpp"
// #include "Tautology.hpp"

using namespace Shell;

/**
 * Preprocess the problem.
 *
 * @since 16/07/2003 hotel Holiday Inn, Moscow, normalization added
 * @since 19/12/2003 Manchester, changed to move preprocessing to units.
 * @since 08/04/2004 Torrevieja pure literal deletion and
 *   clausal definition handling added
 * @since 12/04/2004 Torrevieja tautology and double literal deletion added
 * @since 22/05/2004 Manchester, equality proxy added
 */
void Preprocess::preprocess (UnitList*& units)
{
  CALL("Preprocess::preprocess");

  // before any preprocessing, row variables must be expanded
//   if (RowVariable::occurredInInput &&
//       _options.rowVariableMaxLength() >= 0) {
//     RowVariable rv(_options.rowVariableMaxLength());
//     UnitChain::DelIterator iterator (_problem.giveUnits());
//     while (iterator.hasNext()) {
//       Unit u (iterator.next());
//       if (u.unitType() == FORMULA) {
// 	UnitList us;
// 	if (rv.expandRowVariables(u,us)) {
// 	  ASS(us.isNonEmpty());
// 	  if (us.head() != u) { // there was a row variable expansion
// 	    VL::Iterator<Unit> newUnits(us);
// 	    while (newUnits.hasNext()) {
//   	      iterator.insert(newUnits.next());
// 	    }
// 	    iterator.del();
// 	  }
// 	}
// 	else { // non-expandable row variable found
// 	  iterator.del();
// 	}
//       }
//     }
//   }

  // reorder units
  if (_options.normalize()) {
    Normalisation norm;
    units = norm.normalise(units);
  }

  {
    UnitList::DelIterator us(units);
    while (us.hasNext()) {
      Unit* u = us.next();
      Unit* v = preprocess1(u);
      if (v != u) {
	us.replace(v);
      }
    }
  }

  // discover known theories
//   TheoryFinder theoryFinder(_problem,0);
//   theoryFinder.search();

  if (_options.unusedPredicateDefinitionRemoval()) {
    PredicateDefinition pdRemover;
    pdRemover.removeUnusedDefinitionsAndPurePredicates(units);
  }

  if (_property.hasFormulas()) {
    UnitList::DelIterator us(units);
    while (us.hasNext()) {
      Unit* u = us.next();
      if(u->isClause()) {
	continue;
      }
      Unit* v = preprocess2(u);
      if (v != u) {
	us.replace(v);
      }
    }
  }

  if (_property.hasFormulas() && _options.naming()) {
    UnitList::DelIterator us(units);
    Naming naming(_options.naming());
    while (us.hasNext()) {
      Unit* u = us.next();
      if (u->isClause()) {
	continue;
      }
      UnitList* defs;
      Unit* v = naming.apply(u,defs);
      if (v != u) {
	ASS(defs);
 	us.insert(defs);
	us.replace(v);
      }
    }
  }

  {
    UnitList::DelIterator us(units);
    while (us.hasNext()) {
      Unit* u = us.next();
      Unit* v = preprocess3(u);
      if (v != u) {
	us.replace(v);
      }
    }
  }

//   // find ordering on literals
//   Ordering* ordering = environment.ordering(0);
//   if (ordering) {
//     ordering->fill(Signature::sig);
//   }
//   else {
//     LiteralOrderingFinder lof(_problem,_options,Signature::sig);
//     lof.findOrdering();
//   }

  if (_property.hasFormulas()) {
    UnitList::DelIterator us(units);
    CNF cnf;
    Stack<Clause*> clauses(32);
    while (us.hasNext()) {
      Unit* u = us.next();
      if (! u->isClause()) {
	cnf.clausify(u,clauses);
	while (! clauses.isEmpty()) {
	  Unit* u = clauses.pop();
	  us.insert(u);
	}
	us.del();
      }
    }
  }

  if (_options.functionDefinitionElimination() == Options::FDE_ALL &&
	  _property.hasProp(Property::PR_HAS_FUNCTION_DEFINITIONS)) {
    FunctionDefinition fd;
    fd.removeAllDefinitions(units);
  }

  if (_options.inequalitySplitting() != 0) {
    InequalitySplitting is;
    is.perform(units);
  }

//   // remove tautologies, duplicate literals, and literals t != t
//   UnitChain::DelIterator units (_problem.giveUnits());
//   while (units.hasNext()) {
//     Unit newUnit;
//     switch (Tautology::isTautology(units.next(),newUnit)) {
//     case -1:
//       units.replace(newUnit);
//       break;

//     case 0:
//       break;

//     case 1:
//       units.del();
//       break;
//     }
//   }

//   PureLiteral pure(_problem,Signature::sig);
//   pure.findAndRemove();

//   ClausalDefinition cdef(_problem,Signature::sig);
//   cdef.findAndReplace();

//   if (_property.hasProp(PR_HAS_X_EQUALS_Y)) {
//     switch (_options.equalityProxy()) {
//     case Options::EP_OFF:
//       break;
//     case Options::EP_ON:
//     case Options::EP_EXP1:
//       {
// 	EqualityProxy proxy(Signature::sig);
// 	proxy.apply(_problem);
//       }
//     }
//   }
} // Preprocess::preprocess ()


/**
 * Preprocess the unit using options from opt. Preprocessing may
 * involve inferences and replacement of this unit by a newly inferred one.
 * Preprocessing formula units consists of the following steps:
 * <ol>
 *   <li>Rectify the formula and memorise the answer atom, if necessary.</li>
 *   <li>Flatten the formula.</li>
 * </ol>
 *
 * Preprocessing clause does not change it.
 */
Unit* Preprocess::preprocess1 (Unit* unit)
{
  CALL("Preprocess::preprocess1");

  if (unit->isClause()) {
    return unit;
  }

  // formula unit
  // Rectify the formula and memorise the answer atom, if necessary
  unit = Rectify::rectify(unit);
  // Simplify the formula if it contains true or false
  unit = SimplifyFalseTrue::simplify(unit);
  unit = Flattening::flatten(unit);
  return unit;
} // Preprocess::preprocess1


/**
 * Preprocess the unit using options from opt. Preprocessing may
 * involve inferences and replacement of this unit by a newly inferred one.
 * Preprocessing formula units consists of the following steps:
 * <ol>
 *   <li>Transform the formula to ENNF.</li>
 *   <li>Flatten it.</li>
 * </ol>
 * @since 14/07/2005 flight Tel-Aviv-Barcelona changed to stop before naming
 */
Unit* Preprocess::preprocess2 (Unit* unit)
{
  CALL("Preprocess::preprocess2");
  ASS (! unit->isClause());

  unit = NNF::ennf(unit);
  return Flattening::flatten(unit);
} // Peprocess::preprocess2


/**
 * Preprocess the unit using options from opt. Preprocessing may
 * involve inferences and replacement of this unit by a newly inferred one.
 * Preprocessing formula units consists of the following steps:
 * <ol>
 *   <li>Transform the formula to NNF.</li>
 *   <li>Flatten it.</li>
 *   <li>(Optional) miniscope the formula.</li>
 * </ol>
 * @since 14/07/2005 flight Tel-Aviv-Barcelona
 */
Unit* Preprocess::preprocess3 (Unit* unit)
{
  CALL("Preprocess::preprocess3");

  if (unit->isClause()) {
    return unit;
  }
  // Transform the formula to NNF
  unit = NNF::nnf(unit);
  // flatten it
  unit = Flattening::flatten(unit);
  // (Optional) miniscope the formula
//     if (_options.miniscope()) {
//       Miniscope::miniscope(unit);
//     }
//   return unit;
  return Skolem::skolemise(unit);
} // Peprocess::preprocess3


