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

#include "AIG.hpp"
#include "AIGCompressor.hpp"
#include "AIGConditionalRewriter.hpp"
#include "AIGDefinitionIntroducer.hpp"
#include "AIGInliner.hpp"
#include "AnswerExtractor.hpp"
#include "CNF.hpp"
#include "DistinctGroupExpansion.hpp"
#include "EPRInlining.hpp"
#include "EPRSkolem.hpp"
#include "EqResWithDeletion.hpp"
#include "EqualityPropagator.hpp"
#include "EqualityProxy.hpp"
#include "EquivalenceDiscoverer.hpp"
#include "Flattening.hpp"
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
#include "PredicateIndexIntroducer.hpp"
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

#include "UIHelper.hpp"
#if GNUMP
#include "Lib/List.hpp"
#include "Lib/RCPtr.hpp"
#include "Kernel/Constraint.hpp"
#include "Kernel/Number.hpp"

#include "ConstantRemover.hpp"
#include "EquivalentVariableRemover.hpp"
#include "EqualityVariableRemover.hpp"
#include "HalfBoundingRemover.hpp"
#include "SubsumptionRemover.hpp"

#endif

#include "Lib/List.hpp"
#include "Lib/RCPtr.hpp"
#include "Kernel/Constraint.hpp"
#include "Kernel/Number.hpp"

#include "ConstantRemover.hpp"
#include "EquivalentVariableRemover.hpp"
#include "EqualityVariableRemover.hpp"
#include "HalfBoundingRemover.hpp"
#include "SubsumptionRemover.hpp"

using namespace Shell;
#if GNUMP
/**
 * Bound propagation preprocessing steps. Takes as argumet @c constraints the list of constraints
 * 
 */
void Preprocess::preprocess(ConstraintRCList*& constraints)
{
  CALL("Preprocess::preprocess(ConstraintRCList *& )");

  unfoldEqualities(constraints);
  
  ConstantRemover constantRemover;
  EquivalentVariableRemover evRemover;
  HalfBoundingRemover hbRemover;
  SubsumptionRemover subsRemover;
  EqualityVariableRemover eqRemover;
  bool anyChange;
  do {
    do {
      anyChange = false;

      if (_options.bpEquivalentVariableRemoval()) {
	anyChange |= evRemover.apply(constraints);
      }
      anyChange |= hbRemover.apply(constraints);
      anyChange |= constantRemover.apply(constraints);
      anyChange |= eqRemover.apply(constraints);

    }
    while(anyChange);
    anyChange |= subsRemover.apply(constraints);
  } 
  while(anyChange);
} // Preprocess::preprocess ()

/**
 * Replace equalities by two non-strict inequalities.
 */
void Preprocess::unfoldEqualities(ConstraintRCList*& constraints)
{
  CALL("Preprocess::unfoldEqualities");

  ConstraintRCList::DelIterator cit(constraints);
  while(cit.hasNext()) {
    Constraint& c = *cit.next();
    if (c.type()!=CT_EQ) {
      continue;
    }
   
    ConstraintRCPtr gc(Constraint::clone(c));
    gc->setType(CT_GREQ);
    ConstraintRCPtr lc(Constraint::clone(*gc));
    lc->multiplyCoeffs(CoeffNumber::minusOne());
    
    cit.replace(gc);
    cit.insert(lc);
  }
}
#endif //GNUMP

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
  if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "preprocessing started" << std::endl;
    UnitList::Iterator uit(prb.units());
    while(uit.hasNext()) {
      Unit* u = uit.next();
      env.out() << "[PP] input: " << u->toString() << std::endl;     
    }
  }
  
  //we ensure that in the beginning we have a valid property object, to
  //know that the queries to uncertain problem properties will be precise
  //enough
  prb.getProperty();

  if (prb.hasInterpretedOperations()) {
    env.interpretedOperationsUsed = true;
  }

  if (prb.hasSpecialTermsOrLets()) {
    if (env.options->showPreprocessing())
      env.out() << "special term elimination" << std::endl;

    SpecialTermElimination().apply(prb);
  }
  
  // Expansion of distinct groups happens before other preprocessing
  // If a distinct group is small enough it will add inequality to describe it
  if(env.signature->hasDistinctGroups()){
    if(env.options->showPreprocessing())
      env.out() << "distinct group expansion" << std::endl;
    DistinctGroupExpansion().apply(prb);
  }

  // reorder units
  if (_options.normalize()) {
    env.statistics->phase=Statistics::NORMALIZATION;
    if (env.options->showPreprocessing())
      env.out() << "normalization" << std::endl;
    
    Normalisation().normalise(prb);
  }

  if (_options.sineSelection()!=Options::SineSelection::OFF) {
    env.statistics->phase=Statistics::SINE_SELECTION;
    if (env.options->showPreprocessing())
      env.out() << "sine selection" << std::endl;

    SineSelector(_options).perform(prb);
  }

  if (_options.questionAnswering()==Options::QuestionAnsweringMode::ANSWER_LITERAL) {
    env.statistics->phase=Statistics::UNKNOWN_PHASE;
    if (env.options->showPreprocessing())
      env.out() << "answer literal addition" << std::endl;

    AnswerLiteralManager::getInstance()->addAnswerLiterals(prb);
  }

  if (prb.hasInterpretedOperations() && _options.theoryAxioms()) {
    InterpretedNormalizer().apply(prb);
    env.statistics->phase=Statistics::INCLUDING_THEORY_AXIOMS;
    if (env.options->showPreprocessing())
      env.out() << "adding theory axioms" << std::endl;

    TheoryAxioms().apply(prb);
  }

  // stop here if clausification is not required
  if (!_clausify) {
    return;
  }

  if (prb.mayHaveFormulas()) {
    if (env.options->showPreprocessing())
      env.out() << "preprocess1 (rectify, simplify false true, flatten)" << std::endl;

    preprocess1(prb);
  }

  // discover known theories
//   TheoryFinder theoryFinder(_problem,0);
//   theoryFinder.search();

  if ( _options.equalityPropagation() && prb.mayHaveEquality()) {
    //Another equality propagation is between preprocess2 and preprocess3.
    //the ENNF form there allows us to propagate more equalities.
    //Here we're trying to propagate equalities as well because that might
    //reveal some more formulas to be definitions.
    env.statistics->phase=Statistics::EQUALITY_PROPAGATION;
    if (env.options->showPreprocessing())
      env.out() << "equality propagation" << std::endl;
    
    EqualityPropagator().apply(prb);
  }

  if (_options.predicateIndexIntroduction()) {
    if (env.options->showPreprocessing())
      env.out() << "predicate index introduction" << std::endl;

    PredicateIndexIntroducer().apply(prb);
  }

  if (_options.predicateDefinitionInlining()!=Options::InliningMode::OFF) {
    env.statistics->phase=Statistics::PREDICATE_DEFINITION_INLINING;
    if (env.options->showPreprocessing())
      env.out() << "inlining" << std::endl;

    PDInliner pdInliner(_options.predicateDefinitionInlining()==Options::InliningMode::AXIOMS_ONLY,
	_options.predicateDefinitionInlining()==Options::InliningMode::NON_GROWING);
    pdInliner.apply(prb);

    if (_options.flattenTopLevelConjunctions()) {
      if (env.options->showPreprocessing())
        env.out() << "flattening top-level conjunctions" << std::endl;

        if (TopLevelFlatten().apply(prb)) {
          if (env.options->showPreprocessing())
            env.out() << "inlining" << std::endl;

          PDInliner pdInliner2(_options.predicateDefinitionInlining()==Options::InliningMode::AXIOMS_ONLY,
              _options.predicateDefinitionInlining()==Options::InliningMode::NON_GROWING);
          pdInliner2.apply(prb);
        }
    }
  }
  else if (_options.flattenTopLevelConjunctions()) {
    if (env.options->showPreprocessing())
      env.out() << "flattening top-level conjunctions" << std::endl;

    TopLevelFlatten().apply(prb);
  }


  if (_options.predicateEquivalenceDiscovery()!=Options::PredicateEquivalenceDiscoveryMode::OFF) {
    if (env.options->showPreprocessing())
      env.out() << "equivalence discovery" << std::endl;

    EquivalenceDiscoveringTransformer(_options).apply(prb);
  }

  if (_options.aigFormulaSharing()) {
    if (env.options->showPreprocessing())
      env.out() << "aig formula sharing" << std::endl;

    AIGFormulaSharer().apply(prb);
  }

  if (_options.predicateDefinitionMerging()) {
    env.statistics->phase=Statistics::PREDIACTE_DEFINITION_MERGING;
    if (env.options->showPreprocessing())
      env.out() << "predicate definition merging" << std::endl;

    PDMerger().apply(prb);
  }

  if (_options.eprPreservingSkolemization()) {
    env.statistics->phase=Statistics::EPR_PRESERVING_SKOLEMIZATION;
    if (env.options->showPreprocessing())
      env.out() << "epr skolemization" << std::endl;

    EPRSkolem().apply(prb);
  }

  if (_options.eprRestoringInlining()) {
    env.statistics->phase=Statistics::PREDICATE_DEFINITION_INLINING;
    if (env.options->showPreprocessing())
      env.out() << "epr restoring inlining" << std::endl;

    EPRInlining().apply(prb);
  }

  if (_options.aigBddSweeping()) {
    if (env.options->showPreprocessing())
      env.out() << "bdd sweeping" << std::endl;

    AIGCompressingTransformer().apply(prb);
  }

  if (_options.flattenTopLevelConjunctions()) {
    if (env.options->showPreprocessing())
      env.out() << "flatten top-level conjunctions" << std::endl;    

    TopLevelFlatten().apply(prb);
  }

  if (_options.aigInliner()) {
    if (env.options->showPreprocessing())
      env.out() << "aig inlining" << std::endl;      

    AIGInliner().apply(prb);
  }

  if (_options.aigConditionalRewriting()) {
    if (env.options->showPreprocessing())
      env.out() << "aig conditional rewriting" << std::endl; 

    AIGConditionalRewriter().apply(prb);
  }

  if (_options.aigDefinitionIntroduction()) {
    if (env.options->showPreprocessing())
      env.out() << "aig definition introduction" << std::endl; 

    AIGDefinitionIntroducer(_options.aigDefinitionIntroductionThreshold()).apply(prb);
  }

  if (_options.unusedPredicateDefinitionRemoval()) {
    env.statistics->phase=Statistics::UNUSED_PREDICATE_DEFINITION_REMOVAL;
    if (env.options->showPreprocessing())
      env.out() << "unused predicate definition removal" << std::endl; 

    PredicateDefinition pdRemover;
    pdRemover.removeUnusedDefinitionsAndPurePredicates(prb);
  }

  if (prb.mayHaveFormulas()) {
    if (env.options->showPreprocessing())
      env.out() << "preprocess 2 (ennf,flatten)" << std::endl; 
    
    preprocess2(prb);
  }

  if (_options.equalityPropagation() && prb.mayHaveEquality()) {
    env.statistics->phase=Statistics::EQUALITY_PROPAGATION;
    if (env.options->showPreprocessing())
      env.out() << "equality propagation" << std::endl; 

    EqualityPropagator().apply(prb);
  }

  if (prb.mayHaveFormulas() && _options.naming()) {
    if (env.options->showPreprocessing())
      env.out() << "naming" << std::endl; 

    naming(prb);
  }

  if (prb.mayHaveFormulas()) {
    if (env.options->showPreprocessing())
      env.out() << "preprocess3 (nnf, flatten, skolemize)" << std::endl; 

    preprocess3(prb);
  }

  //we redo the naming if the last naming was restricted by preserving EPR
  if (prb.mayHaveFormulas() && _options.naming() && _options.eprPreservingNaming()) {
    if (env.options->showPreprocessing())
      env.out() << "stage 2 of epr preserving naming" << std::endl; 

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
    if (env.options->showPreprocessing())
      env.out() << "clausify" << std::endl;

    clausify(prb);
  }

  if (prb.mayHaveFunctionDefinitions()) {
    env.statistics->phase=Statistics::FUNCTION_DEFINITION_ELIMINATION;
    if (env.options->showPreprocessing())
      env.out() << "function definition elimination" << std::endl;

    if (_options.functionDefinitionElimination() == Options::FunctionDefinitionElimination::ALL) {
      FunctionDefinition fd;
      fd.removeAllDefinitions(prb);
    }
    else if (_options.functionDefinitionElimination() == Options::FunctionDefinitionElimination::UNUSED) {
      FunctionDefinition::removeUnusedDefinitions(prb);
    }
  }


  if (prb.mayHaveEquality() && _options.inequalitySplitting() != 0) {
    if (env.options->showPreprocessing())
      env.out() << "inequality splitting" << std::endl;

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

   if (_options.equalityResolutionWithDeletion()!=Options::RuleActivity::OFF &&
	   prb.mayHaveInequalityResolvableWithDeletion() ) {
     env.statistics->phase=Statistics::EQUALITY_RESOLUTION_WITH_DELETION;
     if (env.options->showPreprocessing())
      env.out() << "equality resolution with deletion" << std::endl;

     EqResWithDeletion resolver;
     resolver.apply(prb);
   }

   if (_options.trivialPredicateRemoval()) {
     env.statistics->phase=Statistics::UNKNOWN_PHASE;
     if (env.options->showPreprocessing())
      env.out() << "trivial predicate removal" << std::endl;

     TrivialPredicateRemover().apply(prb);
   }

   if (_options.generalSplitting()!=Options::RuleActivity::OFF) {
     env.statistics->phase=Statistics::GENERAL_SPLITTING;
     if (env.options->showPreprocessing())
       env.out() << "general splitting" << std::endl;

     GeneralSplitting gs;
     gs.apply(prb);
   }

   if (_options.hornRevealing()) {
     env.statistics->phase=Statistics::HORN_REVEALING;
     if (env.options->showPreprocessing())
       env.out() << "horn revealing" << std::endl;

     HornRevealer hr(_options);
     hr.apply(prb);
   }

   if (_options.equalityProxy()!=Options::EqualityProxy::OFF && prb.mayHaveEquality() &&
	   prb.mayHaveXEqualsY() ) {
     env.statistics->phase=Statistics::EQUALITY_PROXY;
     if (env.options->showPreprocessing())
       env.out() << "equality proxy" << std::endl;

     EqualityProxy proxy(_options.equalityProxy());
     proxy.apply(prb);
   }

   if (env.options->showPreprocessing()) {
     UnitList::Iterator uit(prb.units());
     while(uit.hasNext()) {
      Unit* u = uit.next();
      env.out() << "[PP] final: " << u->toString() << std::endl;             
     }
   } 

   if (_options.printClausifierPremises()) {
     UIHelper::outputAllPremises(cerr, prb.units());
   }

   if (env.options->showPreprocessing()) {
     env.out() << "preprocessing finished" << std::endl;
     env.endOutput();
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
 *
 * Units passed to preprocess1 must not have any special terms, let..in formulas
 * or terms, or if-then-else terms. It may contain if-then-else formulas.
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
    if (u->isClause()) {
      continue;
    }

    // formula unit
    FormulaUnit* fu = static_cast<FormulaUnit*>(u);
    // Rectify the formula and memorise the answer atom, if necessary
    fu = Rectify::rectify(fu);
    FormulaUnit* rectFu = fu;
    // Simplify the formula if it contains true or false
    fu = SimplifyFalseTrue::simplify(fu);
    if (fu!=rectFu) {
      formulasSimplified = true;
    }
    fu = Flattening::flatten(fu);

    if (fu != u) {
      us.replace(fu);
    }
  }

  if (formulasSimplified) {
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
    if (env.options->showPreprocessing()) {
      env.beginOutput();
      env.out() << "[PP] ennf: " << u->toString() << std::endl;
      env.endOutput();
    }    
    if (u->isClause()) {
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

  if (modified) {
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

  if (modified) {
    prb.invalidateProperty();
  }
} // Preprocess::preprocess3

void Preprocess::clausify(Problem& prb)
{
  CALL("Preprocess::clausify");

  env.statistics->phase=Statistics::CLAUSIFICATION;

  //we check if we haven't discover an empty clause during preprocessing
  Unit* emptyClause = 0;

  bool modified = false;

  UnitList::DelIterator us(prb.units());
  CNF cnf;
  Stack<Clause*> clauses(32);
  while (us.hasNext()) {
    Unit* u = us.next();
    if (env.options->showPreprocessing()) {
      env.beginOutput();
      env.out() << "[PP] clausify: " << u->toString() << std::endl;
      env.endOutput();
    }
    if (u->isClause()) {
      if (static_cast<Clause*>(u)->isEmpty()) {
	emptyClause = u;
	break;
      }
      continue;
    }
    modified = true;
    cnf.clausify(u,clauses);
    while (! clauses.isEmpty()) {
      Unit* u = clauses.pop();
      if (static_cast<Clause*>(u)->isEmpty()) {
	emptyClause = u;
	goto fin;
      }
      us.insert(u);
    }
    us.del();
  }
fin:
  if (emptyClause) {
    prb.units()->destroy();
    prb.units() = 0;
    UnitList::push(emptyClause, prb.units());
  }
  if (modified) {
    prb.invalidateProperty();
  }
  prb.reportFormulasEliminated();
}

