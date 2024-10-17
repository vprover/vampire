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
#include "Lib/IntUnionFind.hpp"

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

  // If there are interpreted operations
  if (prb.hasInterpretedOperations() || env.signature->hasTermAlgebras()){
    // Normalizer is needed, because the TheoryAxioms code assumes Normalized problem
    InterpretedNormalizer().apply(prb);

    // Add theory axioms if needed
    if( _options.theoryAxioms() != Options::TheoryAxiomLevel::OFF){
      env.statistics->phase=Statistics::INCLUDING_THEORY_AXIOMS;
      if (env.options->showPreprocessing())
        std::cout << "adding theory axioms" << std::endl;

      TheoryAxioms(prb).apply();
    }
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

  if (prb.hasInterpretedOperations() || env.signature->hasTermAlgebras()){
    // Some axioms needed to be normalized, so we call InterpretedNormalizer twice
    InterpretedNormalizer().apply(prb);
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

   if (_options.blockedClauseElimination()) {
     env.statistics->phase=Statistics::BLOCKED_CLAUSE_ELIMINATION;
     if(env.options->showPreprocessing())
       std::cout << "blocked clause elimination" << std::endl;

     BlockedClauseElimination bce;
     bce.apply(prb);
   }

   if (_options.softSortsForSaturation()) {
     // TODO: factor out into a separate module
     softSortsForSaturation(prb);
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

void Preprocess::softSortsForSaturation(Problem& prb) {
  // TODO: parts of this could be unified with SortInference::doInference
  // (but that other implementation assumes flattened clasues only)

  // every predicate's symbol argument position and function symbol's argument position or the output position
  // are a priory distinct sort (candidates)
  Array<unsigned> offset_p(env.signature->predicates());
  Array<unsigned> offset_f(env.signature->functions());

  unsigned count = 1; // we make sure 0 is unused
  // skip 0 because it is always equality
  for(unsigned p=1; p < env.signature->predicates();p++){
    offset_p[p] = count;
    Signature::Symbol* s = env.signature->getPredicate(p);

    OperatorType* ot = s->predType();
    if (ot->numTypeArguments()) {
      USER_ERROR("ss4s not supported for polymorphic inputs");
    }

    s->resetUsageCnt();
    count += (s->arity());
  }

  for(unsigned f=0; f < env.signature->functions();f++){
    offset_f[f] = count;
    Signature::Symbol* s = env.signature->getFunction(f);

    OperatorType* ot = s->fnType();
    if (ot->numTypeArguments()) {
      USER_ERROR("ss4s not supported for polymorphic inputs");
    }

    s->resetUsageCnt();
    count += (s->arity()+1);
  }

  Renaming normalizer;
  IntUnionFind unionFind(count);
  Stack<std::pair<unsigned,TermList>> todo; // position, term (which could be a variable or a proper term)

  // each two variable equality (in a clause) deserves to be remembered,
  // along with a position its sort ended up connecting to (or 0, if unconnected)
  Stack<std::tuple<Clause*,unsigned,unsigned>> twoVarEqs;

  UnitList::Iterator it(prb.units());
  while (it.hasNext()) {
    Clause* cl = it.next()->asClause();

    // cout << "Clause: " << cl->toString() << endl;

    // What can we learn by traversing?
    // 1) two positions should be unionified for produce / consume
    // 2) two positions should be unionified for f(...) = g(...)
    // 3) a variable should be unionified with a position (remeber that position with the variable)
    // 4) a variable should be unionified with a variable for X = Y (use local union-find over varaibles)
    // Clauses should remember what their variables ended up meaning

    // (for every orig sort, we may potentially need a new sort for X = Y of that sort,
    // which is otherwise not reflected anywhere else)

    // normalize variables in the clause
    normalizer.reset();
    for(unsigned i=0; i<cl->length(); i++) {
      Literal* l = (*cl)[i];
      normalizer.normalizeVariables(l);
      (*cl)[i] = normalizer.apply(l);
    }

    unsigned cVarCnt = normalizer.nextVar();
    IntUnionFind localUF(cVarCnt+1);
    ZIArray<unsigned> varsPos(cVarCnt);

    for(unsigned i=0; i<cl->length(); i++) {
      Literal* l = (*cl)[i];

      // cout << "Literal: " << l->toString() << endl;

      if (l->isTwoVarEquality()) {
        unsigned v1 = l->nthArgument(0)->var();
        unsigned r1 = localUF.root(v1);
        unsigned v2 = l->nthArgument(1)->var();
        unsigned r2 = localUF.root(v2);

        if (r1 != r2) {
          if (varsPos[r1]) {
            if (varsPos[r2]) {
              // both variables were already connected to a position
              // => make these positions equal globally
              // (we don't need to copy anything anymore)
              unionFind.doUnion(varsPos[r1],varsPos[r2]);
            } else {
              // v1 was connected, now v2 is to the same
              // (we do this, because we don't know who will be the root)
              varsPos[r2] = varsPos[r1];
            }
          } else if (varsPos[r2]) {
            // v2 was connected, now v1 is to the same
            // (we do this, because we don't know who will be the root)
            varsPos[r1] = varsPos[r2];
          }

          localUF.doUnion(v1,v2);
        }
      } else if (l->isEquality()) {
        // Claim: in term sharing, arg 0 of (non twoVar) equality is never a variable
        ASS(!l->nthArgument(0)->isVar());
        Term* t = l->nthArgument(0)->term();
        unsigned f = t->functor();
        env.signature->getFunction(f)->incUsageCnt();
        unsigned p = offset_f[f];
        // cout << "   pair: " << p << " " << l->nthArgument(1)->toString() << endl;
        todo.push(make_pair(p,*l->nthArgument(1))); // could be a var or a proper term

        for(unsigned i=0;i<t->arity();i++){
          p++;
          // cout << "   but also a pair: " << p << " " << t->nthArgument(i)->toString() << endl;
          todo.push(make_pair(p,*t->nthArgument(i)));
        }
      } else {
        unsigned p = l->functor();
        env.signature->getPredicate(p)->incUsageCnt();
        unsigned pos = offset_p[p];
        for(unsigned i=0;i<l->arity();i++){
          todo.push(make_pair(pos,*l->nthArgument(i)));
          pos++;
        }
      }
    }

    while (todo.isNonEmpty()) {
      unsigned p1;
      TermList tl;
      std::tie(p1,tl) = todo.pop();

      // cout << "Process pair: " << p1 << " --> " << unionFind.root(p1) << " " << tl.toString() << endl;

      if (tl.isVar()) {
        unsigned v = tl.var();
        unsigned r = localUF.root(v);

        if (varsPos[r]) {
          unionFind.doUnion(varsPos[r],p1);
        } else {
          varsPos[r] = p1;
        }
      } else {
        Term* t = tl.term();
        unsigned f = t->functor();
        env.signature->getFunction(f)->incUsageCnt();
        unsigned p2 = offset_f[f];
        unionFind.doUnion(p1,p2);

        for(unsigned i=0;i<t->arity();i++){
          p2++;
          todo.push(make_pair(p2,*t->nthArgument(i)));
        }
      }
    }

    for(unsigned i=0; i<cl->length(); i++) {
      Literal* l = (*cl)[i];
      if (l->isTwoVarEquality()) {
        unsigned v1 = l->nthArgument(0)->var();
        unsigned pos = varsPos[localUF.root(v1)];
        twoVarEqs.push(std::make_tuple(cl,i,pos));
      }
    }
  }

  bool modified = false;

  unsigned pos = 0;
  // for those positions that remained as roots:
  DHMap<unsigned,TermList> pos2srt;
  DHSet<TermList> sortTaken;

  auto lookupSortOrGetNew = [&] (unsigned posRoot, TermList origSrt, const std::string& suffix) -> TermList {
    TermList* res;
    if (pos2srt.getValuePtr(posRoot,res)) {
      if (sortTaken.insert(origSrt)) {
        *res = origSrt;
        // cout << "Will reuse " << res->toString() << " for " << posRoot << " origin " << suffix << endl;
      } else {
        unsigned tc;
        std::string nm = origSrt.toString()+"_"+suffix;
        for (;;) {
          bool added;
          tc = env.signature->addTypeCon(nm, 0, added);
          if (added) {
            break;
          } else {
            nm = nm + "_";
          }
        }
        *res = TermList(AtomicSort::createConstant(tc));

        // cout << "Created " << res->toString() << " for " << posRoot << " origin " << suffix << endl;
      }
    } else {
      // cout << "Found " << res->toString() << " for " << posRoot << " origin " << suffix << endl;
    }
    return *res;
  };

  Stack<TermList> sortVec;

  // TODO: we probably don't want to split arithmetic creatures (no matter what)

  for(unsigned p=1; p < env.signature->predicates();p++){
    Signature::Symbol* s = env.signature->getPredicate(p);
    if (s->usageCnt() == 0) { // don't bother touching
      pos += s->arity();
      continue;
    }
    OperatorType* ot = s->predType();
    sortVec.reset();
    for (unsigned i=0; i < s->arity(); i++) {
      pos++;
      sortVec.push(
          lookupSortOrGetNew(unionFind.root(pos),ot->arg(i),"pred_"+s->name()+"-arg"+Int::toString(i))
        );
    }
    OperatorType* new_ot = OperatorType::getPredicateType(s->arity(),sortVec.begin());
    if (ot != new_ot) {
      modified = true;
      s->forceType(new_ot); // will this work?
    }
  }

  for(unsigned f=0; f < env.signature->functions();f++){
    Signature::Symbol* s = env.signature->getFunction(f);

    if (s->usageCnt() == 0) { // don't bother touching
      pos += s->arity()+1;
      continue;
    }
    OperatorType* ot = s->fnType();

    // first is the result sort
    pos++;
    TermList resSrt = lookupSortOrGetNew(unionFind.root(pos),ot->result(),"func_"+s->name()+"-res");

    sortVec.reset();
    for (unsigned i=0; i < s->arity(); i++) {
      pos++;
      sortVec.push(
          lookupSortOrGetNew(unionFind.root(pos),ot->arg(i),"func_"+s->name()+"-arg"+Int::toString(i))
        );
    }
    OperatorType* new_ot = OperatorType::getFunctionType(s->arity(),sortVec.begin(),resSrt);
    if (ot != new_ot) {
      modified = true;
      s->forceType(new_ot); // will this work?
    }
  }

  while (twoVarEqs.isNonEmpty()) {
    auto [cl,i,pos] = twoVarEqs.pop();
    if (pos) {
      TermList* srt;
      NEVER(pos2srt.getValuePtr(unionFind.root(pos),srt));
      Literal* l = (*cl)[i];
      ASS(l->isTwoVarEquality());
      ASS(srt->isTerm());
      if (srt->term() != l->twoVarEqSort().term()) {
        (*cl)[i] = Literal::createEquality(l->polarity(),*l->nthArgument(0),*l->nthArgument(1),*srt);
        modified = true;
      }
    } else {
      // TODO: keep the old sort? Or introduce a new one just for the unconnected X=Y?)
    }
  }

  if (modified) {
    prb.invalidateProperty();
    prb.reportIncompleteTransformation();
  }
}