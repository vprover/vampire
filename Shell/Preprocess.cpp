/**
 * @file Shell/Preprocess.cpp
 * Implements class Preprocess for preprocessing.
 * @since 05/01/2004 Manchester
 * @since 02/06/2007 Manchester, changed to new datastructures
 */

#include "Debug/Tracer.hpp"

#include "Lib/ScopedLet.hpp"

#include "Kernel/Unit.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Problem.hpp"

#include "AnswerExtractor.hpp"
#include "CNF.hpp"
#include "EPRInlining.hpp"
#include "EPRSkolem.hpp"
#include "EqResWithDeletion.hpp"
#include "EqualityPropagator.hpp"
#include "EqualityProxy.hpp"
#include "Flattening.hpp"
#include "FormulaIteExpander.hpp"
#include "FunctionDefinition.hpp"
#include "GeneralSplitting.hpp"
#include "HornRevealer.hpp"
#include "InequalitySplitting.hpp"
#include "InterpretedNormalizer.hpp"
#include "Naming.hpp"
#include "Normalisation.hpp"
#include "NNF.hpp"
#include "Options.hpp"
#include "PDInliner.hpp"
#include "PDMerger.hpp"
#include "PredicateDefinition.hpp"
#include "Preprocess.hpp"
#include "Property.hpp"
#include "Rectify.hpp"
#include "Skolem.hpp"
#include "SimplifyFalseTrue.hpp"
#include "SineUtils.hpp"
#include "Statistics.hpp"
#include "SpecialTermElimination.hpp"
#include "TheoryAxioms.hpp"
#include "TrivialPredicateRemover.hpp"

// #include "Lib/Sort.hpp"
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
void Preprocess::preprocess (Problem& prb)
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

  //we ensure that in the beginning we have a valid property object, to
  //know that the queries to uncertain problem properties will be precise
  //enough
  prb.getProperty();

  if(prb.hasInterpretedOperations()) {
    env.interpretedOperationsUsed = true;
  }

  if(prb.hasSpecialTermsOrLets()) {
    SpecialTermElimination().apply(prb);
  }

  // reorder units
  if (_options.normalize()) {
    env.statistics->phase=Statistics::NORMALIZATION;
    Normalisation().normalise(prb);
  }

  if(_options.sineSelection()!=Options::SS_OFF) {
    env.statistics->phase=Statistics::SINE_SELECTION;
    SineSelector(_options).perform(prb);
  }

  if(_options.questionAnswering()==Options::QA_ANSWER_LITERAL) {
    env.statistics->phase=Statistics::UNKNOWN_PHASE;
    AnswerLiteralManager::getInstance()->addAnswerLiterals(prb);
  }

  if(prb.hasInterpretedOperations()) {
    InterpretedNormalizer().apply(prb);
    env.statistics->phase=Statistics::INCLUDING_THEORY_AXIOMS;
    TheoryAxioms().apply(prb);
  }

  if(prb.mayHaveFormulas()) {
    preprocess1(prb);
  }

  // discover known theories
//   TheoryFinder theoryFinder(_problem,0);
//   theoryFinder.search();

  if(prb.hasFormulaItes()){
    FormulaIteExpander().apply(prb);
  }

  if ( _options.equalityPropagation() && prb.mayHaveEquality()) {
    //Another equality propagation is between preprocess2 and preprocess3.
    //the ENNF form there allows us to propagate more equalities.
    //Here we're trying to propagate equalities as well because that might
    //reveal some more formulas to be definitions.
    env.statistics->phase=Statistics::EQUALITY_PROPAGATION;
    EqualityPropagator().apply(prb);
  }

  if (_options.predicateDefinitionMerging()) {
    env.statistics->phase=Statistics::PREDIACTE_DEFINITION_MERGING;
    PDMerger().apply(prb);
  }

  if (_options.eprPreservingSkolemization()) {
    env.statistics->phase=Statistics::EPR_PRESERVING_SKOLEMIZATION;
    EPRSkolem().apply(prb);
  }

  if (_options.eprRestoringInlining()) {
    env.statistics->phase=Statistics::PREDICATE_DEFINITION_INLINING;
    EPRInlining().apply(prb);
  }

  if (_options.predicateDefinitionInlining()!=Options::INL_OFF) {
    env.statistics->phase=Statistics::PREDICATE_DEFINITION_INLINING;
    PDInliner pdInliner(_options.predicateDefinitionInlining()==Options::INL_AXIOMS_ONLY);
    pdInliner.apply(prb);
  }

  if (_options.unusedPredicateDefinitionRemoval()) {
    env.statistics->phase=Statistics::UNUSED_PREDICATE_DEFINITION_REMOVAL;
    PredicateDefinition pdRemover;
    pdRemover.removeUnusedDefinitionsAndPurePredicates(prb);
  }

  if (prb.mayHaveFormulas()) {
    preprocess2(prb);
  }

  if (_options.equalityPropagation() && prb.mayHaveEquality()) {
    env.statistics->phase=Statistics::EQUALITY_PROPAGATION;
    EqualityPropagator().apply(prb);
  }

  if (prb.mayHaveFormulas() && _options.naming()) {
    naming(prb);
  }

  if (prb.mayHaveFormulas()) {
    preprocess3(prb);
  }

  //we redo the naming if the last naming was restricted by preserving EPR
  if (prb.mayHaveFormulas() && _options.naming() && _options.eprPreservingNaming()) {
    secondStageEprPreservingNaming(prb);
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

  if (prb.mayHaveFormulas()) {
    clausify(prb);
  }

  if(prb.mayHaveFunctionDefinitions()) {
    env.statistics->phase=Statistics::FUNCTION_DEFINITION_ELIMINATION;
    if(_options.functionDefinitionElimination() == Options::FDE_ALL) {
      FunctionDefinition fd;
      fd.removeAllDefinitions(prb);
    }
    else if(_options.functionDefinitionElimination() == Options::FDE_UNUSED) {
      FunctionDefinition::removeUnusedDefinitions(prb);
    }
  }


  if (prb.mayHaveEquality() && _options.inequalitySplitting() != 0) {
    env.statistics->phase=Statistics::INEQUALITY_SPLITTING;
    InequalitySplitting is(_options);
    is.perform(prb);
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

   if (_options.equalityResolutionWithDeletion()!=Options::RA_OFF &&
	   prb.mayHaveInequalityResolvableWithDeletion() ) {
     env.statistics->phase=Statistics::EQUALITY_RESOLUTION_WITH_DELETION;
     EqResWithDeletion resolver;
     resolver.apply(prb);
   }

   if(_options.trivialPredicateRemoval()) {
     env.statistics->phase=Statistics::UNKNOWN_PHASE;
     TrivialPredicateRemover().apply(prb);
   }

   if (_options.equalityProxy()!=Options::EP_OFF && prb.mayHaveEquality() &&
	   (prb.mayHaveXEqualsY() || _options.equalityProxy()!=Options::EP_ON) ) {
     env.statistics->phase=Statistics::EQUALITY_PROXY;
     EqualityProxy proxy(_options.equalityProxy());
     proxy.apply(prb);
   }

   if (_options.generalSplitting()!=Options::RA_OFF) {
     env.statistics->phase=Statistics::GENERAL_SPLITTING;
     GeneralSplitting gs;
     gs.apply(prb);
   }

   if(_options.hornRevealing()) {
     env.statistics->phase=Statistics::HORN_REVEALING;
     HornRevealer hr(_options);
     hr.apply(prb);
   }
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
void Preprocess::preprocess1 (Problem& prb)
{
  CALL("Preprocess::preprocess1");

  ScopedLet<Statistics::ExecutionPhase> epLet(env.statistics->phase, Statistics::PREPROCESS_1);

  bool formulasSimplified = false;

  UnitList*& units = prb.units();

  UnitList::DelIterator us(units);
  while (us.hasNext()) {
    Unit* u = us.next();
    if(u->isClause()) {
      continue;
    }

    // formula unit
    FormulaUnit* fu = static_cast<FormulaUnit*>(u);
    // Rectify the formula and memorise the answer atom, if necessary
    fu = Rectify::rectify(fu);
    FormulaUnit* rectFu = fu;
    // Simplify the formula if it contains true or false
    fu = SimplifyFalseTrue::simplify(fu);
    if(fu!=rectFu) {
      formulasSimplified = true;
    }
    fu = Flattening::flatten(fu);

    if (fu != u) {
      us.replace(fu);
    }
  }

  if(formulasSimplified) {
    prb.invalidateByRemoval();
  }
}


/**
 * Preprocess the units using options from opt. Preprocessing may
 * involve inferences and replacement of this unit by a newly inferred one.
 * Preprocessing formula units consists of the following steps:
 * <ol>
 *   <li>Transform the formula to ENNF.</li>
 *   <li>Flatten it.</li>
 * </ol>
 * @since 14/07/2005 flight Tel-Aviv-Barcelona changed to stop before naming
 */
void Preprocess::preprocess2(Problem& prb)
{
  CALL("Preprocess::preprocess2");

  env.statistics->phase=Statistics::PREPROCESS_2;

  UnitList::DelIterator us(prb.units());
  while (us.hasNext()) {
    Unit* u = us.next();
    if(u->isClause()) {
	continue;
    }
    FormulaUnit* fu = static_cast<FormulaUnit*>(u);
    FormulaUnit* fu0 = fu;

    fu = NNF::ennf(fu);
    fu = Flattening::flatten(fu);


    if (fu != fu0) {
      us.replace(fu);
    }
  }
} // Peprocess::preprocess2

/**
 * Perform naming on problem @c prb which is in ENNF
 */
void Preprocess::naming(Problem& prb)
{
  CALL("Preprocess::naming");
  ASS(_options.naming());

  env.statistics->phase=Statistics::NAMING;
  UnitList::DelIterator us(prb.units());
  Naming naming(_options.naming(), _options.eprPreservingNaming());
  while (us.hasNext()) {
    Unit* u = us.next();
    if (u->isClause()) {
      continue;
    }
    UnitList* defs;
    FormulaUnit* fu = static_cast<FormulaUnit*>(u);
    FormulaUnit* v = naming.apply(fu,defs);
    if (v != fu) {
      ASS(defs);
      us.insert(defs);
      us.replace(v);
    }
  }
  prb.invalidateProperty();
}

/**
 * Perform second stage of epr preserving naming that is done
 * after skolemization and before clausification
 */
void Preprocess::secondStageEprPreservingNaming(Problem& prb)
{
  CALL("Preprocess::secondStageEprPreservingNaming");
  ASS(_options.naming());
  ASS(_options.eprPreservingNaming());

  env.statistics->phase=Statistics::NAMING;

  bool modified = false;

  UnitList::DelIterator us(prb.units());
  Naming naming(min(_options.naming()*2+1,32767), true);
  while (us.hasNext()) {
    Unit* u = us.next();
    if (u->isClause()) {
      continue;
    }
    UnitList* defs;
    FormulaUnit* fu = static_cast<FormulaUnit*>(u);
    FormulaUnit* v = naming.apply(fu,defs);
    if (v != fu) {
      ASS(defs);
      while(defs) {
	Unit* d=preprocess3(UnitList::pop(defs));
	us.insert(new UnitList(d,0));
      }
      us.replace(v);
      modified = true;
    }
  }

  if(modified) {
    prb.invalidateProperty();
  }
}

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
Unit* Preprocess::preprocess3 (Unit* u)
{
  CALL("Preprocess::preprocess3(Unit*)");

  if (u->isClause()) {
    return u;
  }

  FormulaUnit* fu = static_cast<FormulaUnit*>(u);
  // Transform the formula to NNF
  fu = NNF::nnf(fu);
  // flatten it
  fu = Flattening::flatten(fu);
// (Optional) miniscope the formula
//     if (_options.miniscope()) {
//       Miniscope::miniscope(fu);
//     }
//   return unit;
  fu = Skolem::skolemise(fu);
  return fu;
}

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
void Preprocess::preprocess3 (Problem& prb)
{
  CALL("Preprocess::preprocess3(Problem&)");

  bool modified = false;

  env.statistics->phase=Statistics::PREPROCESS_3;
  UnitList::DelIterator us(prb.units());
  while (us.hasNext()) {
    Unit* u = us.next();
    Unit* v = preprocess3(u);
    if (u!=v) {
      us.replace(v);
      modified = true;
    }
  }

  if(modified) {
    prb.invalidateProperty();
  }
} // Preprocess::preprocess3

void Preprocess::clausify(Problem& prb)
{
  CALL("Preprocess::clausify");

  env.statistics->phase=Statistics::CLAUSIFICATION;

  bool modified = false;

  UnitList::DelIterator us(prb.units());
  CNF cnf;
  Stack<Clause*> clauses(32);
  while (us.hasNext()) {
    Unit* u = us.next();
    if (u->isClause()) {
      continue;
    }
    modified = true;
    cnf.clausify(u,clauses);
    while (! clauses.isEmpty()) {
      Unit* u = clauses.pop();
      us.insert(u);
    }
    us.del();
  }
  if(modified) {
    prb.invalidateProperty();
  }
  prb.reportFormulasEliminated();
}

