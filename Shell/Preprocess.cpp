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
 * @file Shell/Preprocess.cpp
 * Implements class Preprocess for preprocessing.
 * @since 05/01/2004 Manchester
 * @since 02/06/2007 Manchester, changed to new datastructures
 */


#include "Lib/ScopedLet.hpp"

#include "Kernel/Unit.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Problem.hpp"

#include "GoalGuessing.hpp"
#include "AnswerLiteralManager.hpp"
#include "CNF.hpp"
#include "NewCNF.hpp"
#include "DistinctGroupExpansion.hpp"
#include "EqResWithDeletion.hpp"
#include "EqualityProxy.hpp"
#include "EqualityProxyMono.hpp"
#include "Flattening.hpp"
#include "FunctionDefinition.hpp"
#include "GeneralSplitting.hpp"
#include "FunctionDefinitionHandler.hpp"
#include "InequalitySplitting.hpp"
#include "InterpretedNormalizer.hpp"
#include "Kernel/ALASCA/Preprocessor.hpp"
#include "Naming.hpp"
#include "Normalisation.hpp"
#include "Shuffling.hpp"
#include "NNF.hpp"
#include "Options.hpp"
#include "PredicateDefinition.hpp"
#include "Preprocess.hpp"
#include "Property.hpp"
#include "Rectify.hpp"
#include "Skolem.hpp"
#include "SimplifyFalseTrue.hpp"
#include "SineUtils.hpp"
#include "Statistics.hpp"
#include "FOOLElimination.hpp"
#include "LambdaElimination.hpp"
#include "TheoryAxioms.hpp"
#include "TheoryFlattening.hpp"
#include "TweeGoalTransformation.hpp"
#include "BlockedClauseElimination.hpp"

#include "UIHelper.hpp"
#include "Lib/List.hpp"

#include "Kernel/TermIterators.hpp"

using namespace std;
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
void Preprocess::preprocess(Problem& prb)
{
  env.options->resolveAwayAutoValues0();

  if(env.options->choiceReasoning()){
    env.signature->addChoiceOperator(env.signature->getChoice());
  }

  if (env.options->showPreprocessing()) {
    std::cout << "preprocessing started" << std::endl;
    UnitList::Iterator uit(prb.units());
    while(uit.hasNext()) {
      Unit* u = uit.next();
      std::cout << "[PP] input: " << u->toString() << std::endl;
    }
  }

  if (_options.questionAnswering()!=Options::QuestionAnsweringMode::OFF) {
    env.statistics->phase=Statistics::ANSWER_LITERAL;
    if (env.options->showPreprocessing())
      std::cout << "answer literal addition" << std::endl;

    AnswerLiteralManager::getInstance()->addAnswerLiterals(prb);
  }

  //we ensure that in the beginning we have a valid property object, to
  //know that the queries to uncertain problem properties will be precise
  //enough
  prb.getProperty();

  if (env.signature->hasDefPreds() &&
      !FunctionDefinitionHandler::isHandlerEnabled(_options)) {
      // if the handler is not requested by any of the relevant options, we preprocess away the special definition parsing immediately
    prb.getFunctionDefinitionHandler().initAndPreprocessEarly(prb);
  }

  /* CAREFUL, keep this at the beginning of the preprocessing pipeline,
   * so that it corresponds to how its done
   * in profileMode() in vampire.cpp and PortfolioMode::searchForProof()
   * to preserve reproducibility out of casc mode when using --decode */
  if (_options.normalize()) { // reorder units
    env.statistics->phase=Statistics::NORMALIZATION;
    if (env.options->showPreprocessing())
      std::cout << "normalization" << std::endl;

    Normalisation().normalise(prb);
  }

  if (_options.shuffleInput()) {
    TIME_TRACE(TimeTrace::SHUFFLING);
    env.statistics->phase=Statistics::SHUFFLING;

    if (env.options->showPreprocessing())
      std::cout << "shuffling1" << std::endl;

    // shuffling at the very beginning
    Shuffling::shuffle(prb);
  }

  if(_options.guessTheGoal() != Options::GoalGuess::OFF){
    prb.invalidateProperty();
    prb.getProperty();
    GoalGuessing().apply(prb);
  }

  // interpreted normalizations are not prepeared for "special" terms, thus it must happen after clausification
  if (prb.hasInterpretedOperations() || env.signature->hasTermAlgebras()){
    if (_options.theoryAxioms() != Options::TheoryAxiomLevel::OFF // we need to normalize before adding the theory axioms as they rely on only normalized symbols being present
      || !_options.alasca()) { // NOTE: Alasca wouldn't need this, but then not all axioms would necessarily be added
      InterpretedNormalizer().apply(prb);
    }

    // Add theory axioms if needed
    if(_options.theoryAxioms() != Options::TheoryAxiomLevel::OFF){
      env.statistics->phase=Statistics::INCLUDING_THEORY_AXIOMS;
      if (env.options->showPreprocessing())
        std::cout << "adding theory axioms" << std::endl;

      TheoryAxioms(prb).apply();
    }
  }

  if (_options.alascaIntegerConversion()) {
    if (env.options->showPreprocessing())
      std::cout << "eliminating euclidean quotient and remainder" << std::endl;

    QuotientEPreproc().proc(prb);
  }


  if (prb.hasFOOL() || prb.isHigherOrder()) {
    // This is the point to extend the signature with $$true and $$false
    // If we don't have fool then these constants get in the way (a lot)

    if (!_options.newCNF() || prb.hasPolymorphicSym() || prb.isHigherOrder()) {
      if (env.options->showPreprocessing())
        std::cout << "FOOL elimination" << std::endl;

      TheoryAxioms(prb).applyFOOL();
      FOOLElimination().apply(prb);
    }
  }

  if(env.options->functionExtensionality() == Options::FunctionExtensionality::AXIOM){
    LambdaElimination::addFunctionExtensionalityAxiom(prb);
  }

  if(env.options->choiceAxiom()){
    LambdaElimination::addChoiceAxiom(prb);
  }

  prb.getProperty();

  if ((prb.hasCombs() || prb.hasAppliedVar()) && env.options->addCombAxioms()){
    LambdaElimination::addCombinatorAxioms(prb);
  }

  if ((prb.hasLogicalProxy() || prb.hasBoolVar()) && env.options->addProxyAxioms()){
    LambdaElimination::addProxyAxioms(prb);
  }

  // Expansion of distinct groups happens before other preprocessing
  // If a distinct group is small enough it will add inequality to describe it
  if(env.signature->hasDistinctGroups()){
    if(env.options->showPreprocessing())
      std::cout << "distinct group expansion" << std::endl;
    DistinctGroupExpansion(_options.distinctGroupExpansionLimit()).apply(prb);
  }

  if (_options.sineToAge() || _options.useSineLevelSplitQueues() || (_options.sineToPredLevels() != Options::PredicateSineLevels::OFF)) {
    env.statistics->phase=Statistics::SINE_SELECTION;

    if (_options.sineToPredLevels() != Options::PredicateSineLevels::OFF) {
      env.predicateSineLevels = new DHMap<unsigned,unsigned>();
    }

    // just to initialize ``env.clauseSineLevels'' or ``env.predicateSineLevels''
    SineSelector(false,_options.sineToAgeTolerance(),0,
        _options.sineToAgeGeneralityThreshold(),true).perform(prb);
  }

  if (_options.sineSelection()!=Options::SineSelection::OFF) {
    env.statistics->phase=Statistics::SINE_SELECTION;
    if (env.options->showPreprocessing())
      std::cout << "sine selection" << std::endl;

    SineSelector(_options).perform(prb);
  }

  // stop here if clausification is not required and still simplify not set
  if (!_clausify && !_stillSimplify) {
    return;
  }

  if (prb.mayHaveFormulas()) {
    if (env.options->showPreprocessing())
      std::cout << "preprocess1 (rectify, simplify false true, flatten)" << std::endl;

    preprocess1(prb);
  }

  if (_options.shuffleInput()) {
   TIME_TRACE(TimeTrace::SHUFFLING);
    env.statistics->phase=Statistics::SHUFFLING;
    if (env.options->showPreprocessing())
      std::cout << "shuffling2" << std::endl;

    // axioms have been added, fool eliminated; moreover, after flattening, more opportunity for shuffling inside
    Shuffling::shuffle(prb);
  }

  // stop here if clausification is not required
  if (!_clausify) {
    return;
  }

  // Remove unused predicates
  // TODO consider if TrivialPredicateRemoval should occur if this is off
  // Two kinds of unused
  // - pure predicates
  // - unused definitions
  // I think TrivialPredicateRemoval just removes pures
  if (_options.unusedPredicateDefinitionRemoval()) {
    env.statistics->phase=Statistics::UNUSED_PREDICATE_DEFINITION_REMOVAL;
    if (env.options->showPreprocessing())
      std::cout << "unused predicate definition removal" << std::endl;

    PredicateDefinition pdRemover;
    pdRemover.removeUnusedDefinitionsAndPurePredicates(prb);
  }

  if (prb.mayHaveFormulas()) {
    if (env.options->showPreprocessing())
      std::cout << "preprocess 2 (ennf,flatten)" << std::endl;

    preprocess2(prb);
  }

  if (_options.shuffleInput()) {
    TIME_TRACE(TimeTrace::SHUFFLING);
    env.statistics->phase=Statistics::SHUFFLING;
    if (env.options->showPreprocessing())
      std::cout << "shuffling3" << std::endl;

    // more flattening -> more shuffling
    Shuffling::shuffle(prb);
  }

  if (prb.mayHaveFormulas() && _options.newCNF() &&
     !prb.hasPolymorphicSym() && !prb.isHigherOrder()) {
    if (env.options->showPreprocessing())
      std::cout << "newCnf" << std::endl;

    newCnf(prb);
  } else {
    if (prb.mayHaveFormulas() && _options.newCNF()) { // TODO: update newCNF to deal with polymorphism / higher-order
      ASS(prb.hasPolymorphicSym() || prb.isHigherOrder());
      if (outputAllowed()) {
        addCommentSignForSZS(std::cout);
        std::cout << "WARNING: Not using newCnf currently not compatible with polymorphic/higher-order inputs." << endl;
      }
    }

    if (prb.mayHaveFormulas() && _options.naming()) {
      if (env.options->showPreprocessing())
        std::cout << "naming" << std::endl;

      naming(prb);
    }

    if (prb.mayHaveFormulas()) {
      if (env.options->showPreprocessing())
        std::cout << "preprocess3 (nnf, flatten, skolemize)" << std::endl;

      preprocess3(prb);
    }

    if (prb.mayHaveFormulas()) {
      if (env.options->showPreprocessing())
        std::cout << "clausify" << std::endl;

      clausify(prb);
    }
  }

  prb.getProperty();


  if (prb.mayHaveFunctionDefinitions()) {
    env.statistics->phase=Statistics::FUNCTION_DEFINITION_ELIMINATION;
    if (env.options->showPreprocessing())
      std::cout << "function definition elimination" << std::endl;

    if (_options.functionDefinitionElimination() == Options::FunctionDefinitionElimination::ALL) {
      FunctionDefinition fd;
      fd.removeAllDefinitions(prb,env.getMainProblem()->isHigherOrder());
    }
    else if (_options.functionDefinitionElimination() == Options::FunctionDefinitionElimination::UNUSED) {
      FunctionDefinition::removeUnusedDefinitions(prb,env.getMainProblem()->isHigherOrder());
    }
  }


  if (prb.mayHaveEquality() && _options.inequalitySplitting() != 0) {
    if (env.options->showPreprocessing())
      std::cout << "inequality splitting" << std::endl;

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

   if (_options.equalityResolutionWithDeletion() && prb.mayHaveInequalityResolvableWithDeletion() ) {
     env.statistics->phase=Statistics::EQUALITY_RESOLUTION_WITH_DELETION;
     if (env.options->showPreprocessing())
      std::cout << "equality resolution with deletion" << std::endl;

     EqResWithDeletion resolver;
     resolver.apply(prb);
   }

   if (env.signature->hasDefPreds() &&
       FunctionDefinitionHandler::isHandlerEnabled(_options)) {
       // if the handler is requested, we preprocess the special definition parsing only after clausification
     prb.getFunctionDefinitionHandler().initAndPreprocessLate(prb,_options);
   }

   if (_options.generalSplitting()) {
     if (prb.isHigherOrder() || prb.hasPolymorphicSym()) {  // TODO: extend GeneralSplitting to support polymorphism (would higher-order make sense?)
       if (outputAllowed()) {
         addCommentSignForSZS(std::cout);
         std::cout << "WARNING: Not using GeneralSplitting currently not compatible with polymorphic/higher-order inputs." << endl;
       }
     } else {
       env.statistics->phase=Statistics::GENERAL_SPLITTING;
       if (env.options->showPreprocessing())
         std::cout << "general splitting" << std::endl;

       GeneralSplitting gs;
       gs.apply(prb);
     }
   }

   if(env.options->tweeGoalTransformation() != Options::TweeGoalTransformation::OFF) {
     env.statistics->phase = Statistics::TWEE;
     if(env.options->showPreprocessing())
       std::cout << "twee goal transformation" << std::endl;

     TweeGoalTransformation twee;
     twee.apply(prb,(env.options->tweeGoalTransformation() == Options::TweeGoalTransformation::GROUND));
   }

   if (!prb.isHigherOrder() && _options.equalityProxy()!=Options::EqualityProxy::OFF && prb.mayHaveEquality()) {
     env.statistics->phase=Statistics::EQUALITY_PROXY;
     if (env.options->showPreprocessing())
       std::cout << "equality proxy" << std::endl;

     // refresh symbol usage counts, can skip unused symbols for equality proxy
     prb.getProperty();
     if(_options.useMonoEqualityProxy() && !prb.hasPolymorphicSym()){
       EqualityProxyMono proxy(_options.equalityProxy());
       proxy.apply(prb);
     } else {
       //default
       EqualityProxy proxy(_options.equalityProxy());
       proxy.apply(prb);
     }
   }


   if(_options.theoryFlattening()) {
     if (prb.hasPolymorphicSym()) { // TODO: extend theoryFlattening to support polymorphism?
       if (outputAllowed()) {
         addCommentSignForSZS(std::cout);
         std::cout << "WARNING: Not using TheoryFlattening currently not compatible with polymorphic inputs." << endl;
       }
     } else {
       if(env.options->showPreprocessing())
         std::cout << "theory flattening" << std::endl;

       TheoryFlattening tf;
       tf.apply(prb);
     }
   }

   if (env.options->alascaIntegerConversion()) {
     if (env.options->showPreprocessing())
        std::cout << "performing integer coversion" << std::endl;

     AlascaPreprocessor alasca(InequalityNormalizer::global());
     alasca.integerConversion(prb);
   }

   if (_options.blockedClauseElimination()) {
     env.statistics->phase=Statistics::BLOCKED_CLAUSE_ELIMINATION;
     if(env.options->showPreprocessing())
       std::cout << "blocked clause elimination" << std::endl;

     BlockedClauseElimination bce;
     bce.apply(prb);
   }

   if (_options.shuffleInput()) {
     TIME_TRACE(TimeTrace::SHUFFLING);
     env.statistics->phase=Statistics::SHUFFLING;
     if (env.options->showPreprocessing())
       std::cout << "shuffling4" << std::endl;

     // cnf and many other things happened - shuffle one more time
     Shuffling::shuffle(prb);
   }

   if (_options.randomPolarities()) {
     TIME_TRACE(TimeTrace::SHUFFLING);
     env.statistics->phase=Statistics::SHUFFLING;
     if (env.options->showPreprocessing())
       std::cout << "flipping polarities" << std::endl;

     Shuffling::polarityFlip(prb);
   }

   if (env.options->showPreprocessing()) {
     UnitList::Iterator uit(prb.units());
     while(uit.hasNext()) {
      Unit* u = uit.next();
      std::cout << "[PP] final: " << u->toString() << std::endl;
     }
   }

   if (_options.printClausifierPremises()) {
     UIHelper::outputAllPremises(cerr, prb.units());
   }

   if (env.options->showPreprocessing()) {
     std::cout << "preprocessing finished" << std::endl;
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
    if (!_options.newCNF() || prb.isHigherOrder() || prb.hasPolymorphicSym()) {
      // NewCNF effectively implements this simplification already (but could have been skipped if higherOrder || hasPolymorphicSym)
      fu = SimplifyFalseTrue::simplify(fu);
    }
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
  env.statistics->phase=Statistics::PREPROCESS_2;

  UnitList::DelIterator us(prb.units());
  while (us.hasNext()) {
    Unit* u = us.next();

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
  ASS(_options.naming());

  env.statistics->phase=Statistics::NAMING;
  UnitList::DelIterator us(prb.units());
  //TODO fix the below
  Naming naming(_options.naming(),false, prb.isHigherOrder()); // For now just force eprPreservingNaming to be false, should update Naming
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
 * Perform the NewCNF algorithm on problem @c prb which is in ENNF
 */
void Preprocess::newCnf(Problem& prb)
{
  env.statistics->phase=Statistics::NEW_CNF;

  // TODO: this is an ugly copy-paste of "Preprocess::clausify"

  //we check if we haven't discovered an empty clause during preprocessing
  Unit* emptyClause = 0;

  bool modified = false;

  UnitList::DelIterator us(prb.units());
  NewCNF cnf(env.options->naming());
  Stack<Clause*> clauses(32);
  while (us.hasNext()) {
    Unit* u = us.next();
    if (env.options->showPreprocessing()) {
      std::cout << "[PP] clausify: " << u->toString() << std::endl;
    }
    if (u->isClause()) {
      if (static_cast<Clause*>(u)->isEmpty()) {
        emptyClause = u;
        break;
      }
      continue;
    }
    modified = true;
    FormulaUnit* fu = static_cast<FormulaUnit*>(u);
    cnf.clausify(fu,clauses);
    while (! clauses.isEmpty()) {
      Clause* cl = clauses.pop();
      if (cl->isEmpty()) {
        emptyClause = cl;
        goto fin;
      }
      us.insert(cl);
    }
    us.del();
  }
  fin:
  if (emptyClause) {
    UnitList::destroy(prb.units());
    prb.units() = 0;
    UnitList::push(emptyClause, prb.units());
  }
  if (modified) {
    prb.invalidateProperty();
  }
  prb.reportFormulasEliminated();
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
Unit* Preprocess::preprocess3 (Unit* u, bool appify /*higher order stuff*/)
{
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
  fu = Skolem::skolemise(fu, appify);
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
  bool modified = false;

  env.statistics->phase=Statistics::PREPROCESS_3;
  UnitList::DelIterator us(prb.units());
  while (us.hasNext()) {
    Unit* u = us.next();
    Unit* v = preprocess3(u, prb.isHigherOrder());
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
  env.statistics->phase=Statistics::CLAUSIFICATION;

  //we check if we haven't discovered an empty clause during preprocessing
  Unit* emptyClause = 0;

  bool modified = false;

  UnitList::DelIterator us(prb.units());
  CNF cnf;
  Stack<Clause*> clauses(32);
  while (us.hasNext()) {
    Unit* u = us.next();
    if (env.options->showPreprocessing()) {
      std::cout << "[PP] clausify: " << u->toString() << std::endl;
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
    UnitList::destroy(prb.units());
    prb.units() = 0;
    UnitList::push(emptyClause, prb.units());
  }
  if (modified) {
    prb.invalidateProperty();
  }
  prb.reportFormulasEliminated();
}
