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
 * @file vampire.cpp. Implements the top-level procedures of Vampire.
 */

#include <iostream>
#include <ostream>
#include <fstream>
#include <csignal>
#include <string>

#if VZ3
#include "z3++.h"
#endif

#include "Debug/Tracer.hpp"

#include "Lib/Exception.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/MapToLIFO.hpp"
#include "Lib/Random.hpp"
#include "Lib/Set.hpp"
#include "Lib/Stack.hpp"
#include "Lib/TimeCounter.hpp"
#include "Lib/Timer.hpp"
#include "Lib/VString.hpp"
#include "Lib/List.hpp"
#include "Lib/Vector.hpp"
#include "Lib/System.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/STL.hpp"

#include "Lib/RCPtr.hpp"


#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"

#include "Indexing/TermSharing.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Inferences/TautologyDeletionISE.hpp"
#include "SATSubsumption/SMTSubsumption.hpp"
#include "SATSubsumption/cdebug.hpp"

//#include "InstGen/IGAlgorithm.hpp"

#include "SAT/DIMACS.hpp"

#include "CASC/PortfolioMode.hpp"
#include "CASC/CLTBMode.hpp"
#include "CASC/CLTBModeLearning.hpp"
#include "Shell/CommandLine.hpp"
//#include "Shell/EqualityProxy.hpp"
#include "Shell/Grounding.hpp"
#include "Shell/Normalisation.hpp"
#include "Shell/Options.hpp"
#include "Shell/Property.hpp"
#include "Saturation/ProvingHelper.hpp"
#include "Shell/Preprocess.hpp"
#include "Shell/TheoryFinder.hpp"
#include "Shell/TPTPPrinter.hpp"
#include "Parse/TPTP.hpp"
#include "Shell/FOOLElimination.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/UIHelper.hpp"
#include "Shell/LaTeX.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "SAT/MinisatInterfacing.hpp"
#include "SAT/MinisatInterfacingNewSimp.hpp"

#include "FMB/ModelCheck.hpp"
#include <thread>

#if CHECK_LEAKS
#include "Lib/MemoryLeak.hpp"
#endif

#define USE_SPIDER 0
#define SAVE_SPIDER_PROPERTIES 0

using namespace Shell;
using namespace SAT;
using namespace Saturation;
using namespace Inferences;
//using namespace InstGen;

/**
 * Return value is non-zero unless we were successful.
 *
 * Being successful for modes that involve proving means that we have
 * either found refutation or established satisfiability.
 *
 *
 * If Vampire was interrupted by a SIGINT, value
 * VAMP_RESULT_STATUS_SIGINT is returned,
 * and in case of other signal we return VAMP_RESULT_STATUS_OTHER_SIGNAL. For implementation
 * of these return values see Lib/System.hpp.
 *
 * In case of an unhandled exception or user error, we return value
 * VAMP_RESULT_STATUS_UNHANDLED_EXCEPTION.
 *
 * In case Vampire was terminated by the timer, return value is
 * uncertain (but definitely not zero), probably it will be 134
 * (we terminate by a call to the @b abort() function in this case).
 */
int vampireReturnValue = VAMP_RESULT_STATUS_UNKNOWN;

/**
 * Return value is non-zero unless we were successful.
 *
 * Being successful for modes that involve proving means that we have
 * either found refutation or established satisfiability.
 *
 *
 * If execution was interrupted by a SIGINT, value 3 is returned,
 * and in case of other signal we return 2. For implementation
 * of these return values see Lib/System.hpp.
 *
 * In case execution was terminated by the timer, return value is 1.
 * (see @c timeLimitReached() in Lib/Timer.cpp)
 */
int g_returnValue = 1;

/**
 * Preprocess input problem
 *
 */
Problem* getPreprocessedProblem()
{
  CALL("getPreprocessedProblem");

  Problem* prb = UIHelper::getInputProblem(*env.options);

  TimeCounter tc2(TC_PREPROCESSING);

  Shell::Preprocess prepro(*env.options);
  //phases for preprocessing are being set inside the preprocess method
  prepro.preprocess(*prb);

  // TODO: could this be the right way to freeing the currently leaking classes like Units, Clauses and Inferences?
  // globUnitList = prb->units();

  return prb;
} // getPreprocessedProblem

void explainException(Exception& exception)
{
  env.beginOutput();
  exception.cry(env.out());
  env.endOutput();
} // explainException

void getRandomStrategy()
{
  CALL("getRandomStrategy()");
  // We might have set random_strategy sat
  if(env.options->randomStrategy()==Options::RandomStrategy::OFF){
    env.options->setRandomStrategy(Options::RandomStrategy::ON);
  }

  // One call to randomize before preprocessing (see Options)
  env.options->randomizeStrategy(0);
  ScopedPtr<Problem> prb(getPreprocessedProblem());
  // Then again when the property is here
  env.options->randomizeStrategy(prb->getProperty());

  // It is possible that the random strategy is still incorrect as we don't
  // have access to the Property when setting preprocessing
  env.options->checkProblemOptionConstraints(prb->getProperty());
}

void doProving()
{
  CALL("doProving()");
  // One call to randomize before preprocessing (see Options)
  env.options->randomizeStrategy(0);

  ScopedPtr<Problem> prb(getPreprocessedProblem());

  // Then again when the property is here (this will only randomize non-default things if an option is set to do so)
  env.options->randomizeStrategy(prb->getProperty());

  // this will provide warning if options don't make sense for problem
  //env.options->checkProblemOptionConstraints(prb->getProperty());

  ProvingHelper::runVampireSaturation(*prb, *env.options);
}

/**
 * Read a problem and output profiling information about it.
 * @since 03/08/2008 Torrevieja
 */
void profileMode()
{
  CALL("profileMode()");

  ScopedPtr<Problem> prb(UIHelper::getInputProblem(*env.options));

  /* CAREFUL: Make sure that the order
   * 1) getProperty, 2) normalise, 3) TheoryFinder::search
   * is the same as in PortfolioMode::searchForProof
   * also, cf. the beginning of Preprocessing::preprocess*/
  Property* property = prb->getProperty();
  Normalisation().normalise(*prb);
  TheoryFinder(prb->units(), property).search();

  env.beginOutput();
  env.out() << property->categoryString() << ' ' << property->props() << ' '
	  << property->atoms() << "\n";
  env.endOutput();

  //we have succeeded with the profile mode, so we'll terminate with zero return value
  vampireReturnValue = VAMP_RESULT_STATUS_SUCCESS;
} // profileMode

void outputResult(ostream& out) {
  CALL("outputResult");

  switch(env.statistics->terminationReason) {
  case Statistics::UNKNOWN:
    cout<<"unknown"<<endl;
    break;
  case Statistics::INAPPROPRIATE:
    cout<<"inappropriate"<<endl;
    break;
  case Statistics::SATISFIABLE:
    cout<<"sat"<<endl;
    break;
  case Statistics::REFUTATION:
    cout<<"unsat"<<endl;
    break;
  default:
    //these outcomes are not reachable with the current implementation
    ASSERTION_VIOLATION;
  }
  if(env.options->mode()!=Options::Mode::SPIDER){
    env.statistics->print(env.out());
  }
}

// prints Unit u at an index to latexOut using the LaTeX object
void outputUnitToLaTeX(LaTeX& latex, ofstream& latexOut, Unit* u,unsigned index)
{
    vstring stringform = latex.toString(u);
    latexOut << index++ << " & ";
    unsigned count = 0;
    for(const char* p = stringform.c_str();*p;p++){
      latexOut << *p;
      count++;
      if(count>80 && *p==' '){
        latexOut << "\\\\ \n & ~~~~~";
        count=0;
      }
    }
    latexOut << "\\\\" << endl;
}

// print the clauses of a problem to a LaTeX file
void outputClausesToLaTeX(Problem* prb)
{
  CALL("outputClausesToLaTeX");
  ASS(env.options->latexOutput()!="off");

  BYPASSING_ALLOCATOR; // not sure why we need this yet, ofstream?

  LaTeX latex;
  ofstream latexOut(env.options->latexOutput().c_str());
  latexOut << latex.header() << endl;
  latexOut << "\\section{Problem "<<env.options->problemName() << "}" << endl;
  //TODO output more header
  latexOut << "\\[\n\\begin{array}{ll}" << endl;

  CompositeISE simplifier;
  simplifier.addFront(new TrivialInequalitiesRemovalISE());
  simplifier.addFront(new TautologyDeletionISE());
  simplifier.addFront(new DuplicateLiteralRemovalISE());

  unsigned index=0;
  ClauseIterator cit = prb->clauseIterator();
  while (cit.hasNext()) {
    Clause* cl = cit.next();
    cl = simplifier.simplify(cl);
    if (!cl) {
      continue;
    }
    outputUnitToLaTeX(latex,latexOut,cl,index++);
  }
  latexOut  << "\\end{array}\n\\]" << latex.footer() << "\n";

  //close ofstream?
}

// print the formulas of a problem to a LaTeX file
void outputProblemToLaTeX(Problem* prb)
{
  CALL("outputProblemToLaTeX");
  ASS(env.options->latexOutput()!="off");

  BYPASSING_ALLOCATOR; // not sure why we need this yet, ofstream?

  LaTeX latex;
  ofstream latexOut(env.options->latexOutput().c_str());
  latexOut << latex.header() << endl;
  latexOut << "\\section{Problem "<<env.options->problemName() << "}" << endl;
  //TODO output more header
  latexOut << "\\[\n\\begin{array}{ll}" << endl;

  //TODO  get symbol and sort declarations into LaTeX
  //UIHelper::outputSortDeclarations(env.out());
  //UIHelper::outputSymbolDeclarations(env.out());

  UnitList::Iterator units(prb->units());

  unsigned index = 0;
  while (units.hasNext()) {
    Unit* u = units.next();
    outputUnitToLaTeX(latex,latexOut,u,index++);
  }
  latexOut  << "\\end{array}\n\\]" << latex.footer() << "\n";

  //close ofstream?
}

/**
 * This mode only preprocesses the input using the current preprocessing
 * options and outputs it to stdout. It is useful for either preprocessing
 * per se or also for converting one syntax to another. For the latter, the input
 * and the output syntaxes must be set to different values. Note that for
 * simply translating one syntax to another, output mode is the right one.
 *
 * @author Andrei Voronkov
 * @since 02/07/2013 Manchester
 */
void preprocessMode(bool theory)
{
  CALL("preprocessMode()");

  Problem* prb = UIHelper::getInputProblem(*env.options);

  TimeCounter tc2(TC_PREPROCESSING);

  // preprocess without clausification
  Shell::Preprocess prepro(*env.options);
  prepro.turnClausifierOff();
  if(env.options->mode() == Options::Mode::PREPROCESS2){
    prepro.keepSimplifyStep();
  }
  prepro.preprocess(*prb);

  env.beginOutput();
  //outputSymbolDeclarations also deals with sorts for now
  //UIHelper::outputSortDeclarations(env.out());
  UIHelper::outputSymbolDeclarations(env.out());
  UnitList::Iterator units(prb->units());
  while (units.hasNext()) {
    Unit* u = units.next();
    if (!env.options->showFOOL()) {
      if (u->inference().rule() == InferenceRule::FOOL_AXIOM_TRUE_NEQ_FALSE || u->inference().rule() == InferenceRule::FOOL_AXIOM_ALL_IS_TRUE_OR_FALSE) {
        continue;
      }
    }

    if (theory) {
      Formula* f = u->getFormula();

      // CONJECTURE as inputType is evil, as it cannot occur multiple times
      if (u->inference().inputType() == UnitInputType::CONJECTURE) {
        u->inference().setInputType(UnitInputType::NEGATED_CONJECTURE);
      }

      FormulaUnit* fu = new FormulaUnit(f,u->inference()); // we are stealing u's inference which is not nice
      env.out() << TPTPPrinter::toString(fu) << "\n";
    } else {
      env.out() << TPTPPrinter::toString(u) << "\n";
    }
  }
  env.endOutput();

  if(env.options->latexOutput()!="off"){ outputProblemToLaTeX(prb); }

  //we have successfully output all clauses, so we'll terminate with zero return value
  vampireReturnValue = VAMP_RESULT_STATUS_SUCCESS;
} // preprocessMode

/**
 *
 * @author Giles
 * @since 6/10/2015
 */
void modelCheckMode()
{
  CALL("modelCheckMode");

  env.options->setOutputAxiomNames(true);
  Problem* prb = UIHelper::getInputProblem(*env.options);

  if(env.statistics->polymorphic || env.statistics->higherOrder){
    USER_ERROR("Polymorphic Vampire is not yet compatible with theory reasoning");
  }

  FMB::ModelCheck::doCheck(prb);

} // modelCheckMode


/**
 * This mode only outputs the input problem. It is useful for converting
 * one syntax to another.
 * @author Laura Kovacs and Andrei Voronkov
 * @since 02/07/2013 Gothenburg and Manchester
 */
void outputMode()
{
  CALL("outputMode()");

  Problem* prb = UIHelper::getInputProblem(*env.options);

  env.beginOutput();
  //outputSymbolDeclarations also deals with sorts for now
  //UIHelper::outputSortDeclarations(env.out());
  UIHelper::outputSymbolDeclarations(env.out());
  UnitList::Iterator units(prb->units());

  while (units.hasNext()) {
    Unit* u = units.next();
    env.out() << TPTPPrinter::toString(u) << "\n";
  }
  env.endOutput();

  if(env.options->latexOutput()!="off"){ outputProblemToLaTeX(prb); }

  //we have successfully output all clauses, so we'll terminate with zero return value
  vampireReturnValue = VAMP_RESULT_STATUS_SUCCESS;
} // outputMode

void vampireMode()
{
  CALL("vampireMode()");

  if (env.options->mode() == Options::Mode::CONSEQUENCE_ELIMINATION) {
    env.options->setUnusedPredicateDefinitionRemoval(false);
  }

  doProving();

  env.beginOutput();
  UIHelper::outputResult(env.out());
  env.endOutput();

  if (env.statistics->terminationReason == Statistics::REFUTATION
      || env.statistics->terminationReason == Statistics::SATISFIABLE) {
      vampireReturnValue = VAMP_RESULT_STATUS_SUCCESS;
  }
} // vampireMode



bool subsumptionBenchmarkMode_parseAxiomName(vstring const& name, vstring const& prefix, std::pair<unsigned int, bool>& out_result)
{
  vstring const success_suffix = "_success";
  vstring const failure_suffix = "_failure";

  if (std::strncmp(name.c_str(), prefix.c_str(), prefix.size()) == 0) {
    char* end = nullptr;
    unsigned int number = std::strtoul(name.c_str() + prefix.size(), &end, 10);
    if (std::strncmp(end, success_suffix.c_str(), success_suffix.size()) == 0) {
      out_result = {number, true};
      return true;
    } else if (std::strncmp(end, failure_suffix.c_str(), failure_suffix.size()) == 0) {
      out_result = {number, false};
      return true;
    } else {
      throw UserErrorException("Unexpected suffix of axiom name: ", name);
    }
  } else {
    return false;
  }
}

vvector<SMTSubsumption::SubsumptionInstance> getOldFormatSubsumptionInstances(UnitList const* units)
{
  // Components of key: sequence number, whether side premise subsumes main premise
  using Key = std::pair<unsigned int, bool>;

  vmap<Key, Clause*> side_premises;
  vmap<Key, Clause*> main_premises;

  while (UnitList::isNonEmpty(units)) {
    Clause* clause = units->head()->asClause();
    // std::cerr << "Clause: " << clause->toString() << std::endl;

    Unit* unit = clause;
    while (true) {
      auto const& inference = unit->inference();
      auto parents = inference.iterator();
      if (!inference.hasNext(parents)) {
        // no parents -> we have an axiom
        vstring name;
        Parse::TPTP::findAxiomName(unit, name);

        Key k{0, false};
        if (name == "side_premise") {
          bool inserted = side_premises.insert({k, clause}).second;
          if (!inserted) { USER_ERROR("duplicate 'side_premise'"); }
        } else if (name == "main_premise") {
          bool inserted = main_premises.insert({k, clause}).second;
          if (!inserted) { USER_ERROR("duplicate 'main_premise'"); }
        } else if (subsumptionBenchmarkMode_parseAxiomName(name, "side_premise_", k)) {
          auto res = side_premises.insert({k, clause});
          bool inserted = res.second;
          if (!inserted) {
            throw UserErrorException("Duplicate side premise for key: {", k.first, ",", k.second, "}");
          }
        } else if (subsumptionBenchmarkMode_parseAxiomName(name, "main_premise_", k)) {
          auto res = main_premises.insert({k, clause});
          bool inserted = res.second;
          if (!inserted) {
            throw UserErrorException("Duplicate main premise for key: {", k.first, ",", k.second, "}");
          }
        } else {
          throw UserErrorException("Unexpected axiom: ", unit->toString());
        }
        break;
      } else {
        // There's still parents to process
        Unit* parent = inference.next(parents);
        ASS(!inference.hasNext(parents));  // we expect exactly one parent
        unit = parent;
      }
    }

    units = units->tail();
  }

  vvector<SMTSubsumption::SubsumptionInstance> instances;

  for (auto p : side_premises) {
    Key k = p.first;
    Clause* side_premise = p.second;
    auto lookup = main_premises.find(k);
    if (lookup == main_premises.end()) {
      throw UserErrorException("Got side premise but no main premise for key: {", k.first, ",", k.second, "}");
    }
    Clause* main_premise = lookup->second;

    ASS_NEQ(side_premise, main_premise);

    instances.push_back({
      .side_premise = side_premise,
      .main_premise = main_premise,
      .number = k.first,
      .result = k.second,
    });
  }

  // The parser reverses the order of literals in the clause as given in the input file, so we correct this here
  DHSet<Clause*> seen;
  for (auto instance : instances) {
    Clause* side_premise = instance.side_premise;
    if (seen.insert(side_premise)) {
      std::reverse(side_premise->literals(), side_premise->literals() + side_premise->length());
    }
    Clause* main_premise = instance.main_premise;
    if (seen.insert(main_premise)) {
      std::reverse(main_premise->literals(), main_premise->literals() + main_premise->length());
    }
  }

  if (instances.size() != main_premises.size()) {
    ASS(instances.size() < main_premises.size());
    throw UserErrorException("Got main premise without corresponding side premise");
  }
  ASS_EQ(instances.size(), side_premises.size());

  return instances;
}

vmap<unsigned int, Clause*> getNumberedClauses(UnitList const* units)
{
  vmap<unsigned int, Clause*> clauses;

  while (UnitList::isNonEmpty(units)) {
    Clause* clause = units->head()->asClause();
    // std::cerr << "Clause: " << clause->toString() << std::endl;

    Unit* unit = clause;
    while (true) {
      auto const& inference = unit->inference();
      auto parents = inference.iterator();
      if (!inference.hasNext(parents)) {
        // no parents -> we have an axiom
        vstring name;
        Parse::TPTP::findAxiomName(unit, name);

        vstring prefix = "clause_";
        if (std::strncmp(name.c_str(), prefix.c_str(), prefix.size()) == 0) {
          unsigned int number = std::strtoul(name.c_str() + prefix.size(), nullptr, 10);
          bool inserted = clauses.insert({number, clause}).second;
          if (!inserted) {
             throw UserErrorException("duplicate clause with number: ", number);
          }
        }
        // done with this clause, go to the next one
        break;
      } else {
        // There's still parents to process
        Unit* parent = inference.next(parents);
        ASS(!inference.hasNext(parents));  // we expect exactly one parent
        unit = parent;
      }
    }

    units = units->tail();
  }

  // The parser reverses the order of literals in the clause as given in the input file, so we correct this here
  DHSet<Clause*> seen;
  for (auto& pair : clauses) {
    Clause* clause = pair.second;
    if (seen.insert(clause)) {
      std::reverse(clause->literals(), clause->literals() + clause->length());
    }
  }

  return clauses;
}

SMTSubsumption::SubsumptionBenchmark getSubsumptionBenchmark(UnitList const* units)
{
  BYPASSING_ALLOCATOR;
  SMTSubsumption::SubsumptionBenchmark b;

  vstring slog_path = env.options->subsumptionLogfile();
  if (slog_path.empty()) {
    // USER_ERROR("No subsumption log!");
    std::cerr << "\% Parsing old-style subsumption log..." << std::endl;
    b.subsumptions = getOldFormatSubsumptionInstances(units);
    return b;
  }

  std::cerr << "\% Parsing subsumption log..." << std::endl;
  unsigned int number = 0;
  auto clauses = getNumberedClauses(units);
  std::ifstream slog{slog_path.c_str()};
  bool round_is_empty = true;
  Kernel::Clause* main_premise = nullptr;
  while (true) {
    // parse slog line:
    // - next round:
    //   R
    // - subsumption:
    //   S <side_premise_number> <main_premise_number> <result>
    // - subsumption resolution:
    //   SR <side_premise_number> <main_premise_number> <res_lit_idx> <result>
    std::string buf;
    if (!(slog >> buf)) {
      break;
    }
    if (buf == "R") {
      if (!round_is_empty) {
        if (b.subsumptions.size() > (size_t)UINT_MAX) { USER_ERROR("too many subsumptions!"); }
        if (b.subsumptionResolutions.size() > (size_t)UINT_MAX) { USER_ERROR("too many subsumption resolutions!"); }
        b.rounds.emplace_back();
        b.rounds.back().s_end = b.subsumptions.size();
        b.rounds.back().sr_end = b.subsumptionResolutions.size();
        round_is_empty = true;
      }
      unsigned int main_premise_number;
      if (!(slog >> main_premise_number)) {
        USER_ERROR("expected <main_premise_number>");
      }
      main_premise = clauses.at(main_premise_number);
      number += 1;
    }
    else if (buf == "S") {
      unsigned int side_premise_number;
      if (!(slog >> side_premise_number)) {
        USER_ERROR("expected <side_premise_number>");
      }
      int result;
      if (!(slog >> result)) {
        std::cerr << "expected <result> (continue with 'unknown' value)" << std::endl;
        result = -3;
      }
      b.subsumptions.push_back({
          .side_premise = clauses.at(side_premise_number),
          .main_premise = main_premise,
          .number = ++number,
          .result = result,
      });
      round_is_empty = false;
    }
    else if (buf == "SR") {
      unsigned int side_premise_number;
      if (!(slog >> side_premise_number)) {
        USER_ERROR("expected <side_premise_number>");
      }
      if (!(slog >> buf)) {
        USER_ERROR("expected <res_lit_idx>");
      }
      unsigned int res_lit_idx;
      if (buf == "*") {
        res_lit_idx = UINT_MAX;
      } else {
        res_lit_idx = std::stoul(buf);
      }
      int result;
      if (!(slog >> result)) {
        std::cerr << "expected <result> (continue with 'unknown' value)" << std::endl;
        result = -3;
      }
      b.subsumptionResolutions.push_back({
          .side_premise = clauses.at(side_premise_number),
          .main_premise = main_premise,
          .res_lit = res_lit_idx,
          .number = ++number,
          .result = result,
      });
      round_is_empty = false;
    }
    else {
      USER_ERROR("expected 'R', 'S', or 'SR'");
    }
  }
  if (!round_is_empty) {
    b.rounds.emplace_back();
    b.rounds.back().s_end = b.subsumptions.size();
    b.rounds.back().sr_end = b.subsumptionResolutions.size();
    round_is_empty = true;
  }
  return b;
}


/// Handle modes 'sbench-micro' and 'sbench-run'
void subsumptionBenchmarkMode(bool simulate_full_run)
{
  CALL("subsumptionBenchmarkMode(bool)");
  Timer::setLimitEnforcement(false);  // don't terminate in signal handler

  std::cerr << "\% Subsumption Benchmark Mode\n\% Parsing input..." << std::endl;

  // env.options->setNormalize(false);
  // env.options->setUnusedPredicateDefinitionRemoval(false);

  // We need to set this option to make the parser save axiom names
  env.options->setOutputAxiomNames(true);

  ScopedPtr<Problem> prb(UIHelper::getInputProblem(*env.options));

  Shell::Preprocess prepro(*env.options);
  prepro.preprocess_very_lightly(*prb);

  auto b = getSubsumptionBenchmark(prb->units());

  long n_total = 0;
  long n_sat = 0;
  long n_unsat = 0;
  long n_unknown = 0;
  for (auto const& s : b.subsumptions) {
    n_total += 1;
    if (s.result == 0) {
      n_unsat += 1;
    } else if (s.result == 1) {
      n_sat += 1;
    } else if (s.result < 0) {
      n_unknown += 1;
    } else {
      n_sat = std::numeric_limits<long>::min();
      n_unsat = std::numeric_limits<long>::min();
      n_unknown = std::numeric_limits<long>::min();
      std::cerr << "got unexpected result" << std::endl;
    }
  }
  std::cerr << "Subsumption SAT vs. UNSAT: total= " << n_total << " sat= " << n_sat << " unsat= " << n_unsat << " unknown= " << n_unknown << std::endl;

  SMTSubsumption::ProofOfConcept s;
  if (simulate_full_run) {
    s.benchmark_run(std::move(b));
  } else {
    s.benchmark_micro(std::move(b));
  }

  vampireReturnValue = VAMP_RESULT_STATUS_SUCCESS;
}

/// Handle mode 'stest'
void subsumptionTestingMode()
{
  CALL("subsumptionTestingMode()");
  Timer::setLimitEnforcement(false);  // don't terminate in signal handler

  // env.options->setNormalize(false);
  // env.options->setUnusedPredicateDefinitionRemoval(false);

  // We need to set this option to make the parser save axiom names
  env.options->setOutputAxiomNames(true);

  ScopedPtr<Problem> prb(UIHelper::getInputProblem(*env.options));

  Shell::Preprocess prepro(*env.options);
  prepro.preprocess_very_lightly(*prb);

  auto b = getSubsumptionBenchmark(prb->units());
  auto instances = b.subsumptions;

  if (instances.size() != 1) {
    std::cerr << "stest: got " << instances.size() << " instances, will use the first one." << std::endl;
  }

  auto instance = instances.at(0);

  SMTSubsumption::ProofOfConcept s;
  s.test(instance.side_premise, instance.main_premise);

  vampireReturnValue = VAMP_RESULT_STATUS_SUCCESS;
}





void spiderMode()
{
  CALL("spiderMode()");
  env.options->setBadOptionChoice(Options::BadOption::HARD);
  env.options->setOutputMode(Options::Output::SPIDER);
  Exception* exception = 0;
#if VZ3
  z3::exception* z3_exception = 0;
#endif
  bool noException = true;
  try {
    doProving();
  } catch (Exception& e) {
    exception = &e;
    noException = false;
#if VZ3
  } catch(z3::exception& e){
    z3_exception = &e;
    noException = false;
#endif
  } catch (...) {
    noException = false;
  }

  env.beginOutput();
  if (noException) {
    switch (env.statistics->terminationReason) {
    case Statistics::REFUTATION:
      reportSpiderStatus('+');
      vampireReturnValue = VAMP_RESULT_STATUS_SUCCESS;
      break;
    case Statistics::TIME_LIMIT:
      reportSpiderStatus('t');
    case Statistics::MEMORY_LIMIT:
      reportSpiderStatus('m');
    case Statistics::UNKNOWN:
    case Statistics::INAPPROPRIATE:
      reportSpiderStatus('u');
    case Statistics::REFUTATION_NOT_FOUND:
      if(env.statistics->discardedNonRedundantClauses>0){
        reportSpiderStatus('n');
      }
      else{
        reportSpiderStatus('i');
      }
      break;
    case Statistics::SATISFIABLE:
      reportSpiderStatus('-');
      vampireReturnValue = VAMP_RESULT_STATUS_SUCCESS;
      break;
    default:
      ASSERTION_VIOLATION;
    }
    // env.statistics->print(env.out());
  } else {
#if VZ3
    if(z3_exception){
      if(strcmp(z3_exception->msg(),"out of memory\n")){
        reportSpiderStatus('m');
      }
      else{ reportSpiderFail(); }
    }
    else{
#endif
      reportSpiderFail();
      ASS(exception);
      explainException(*exception);
#if VZ3
    }
#endif
    vampireReturnValue = VAMP_RESULT_STATUS_UNHANDLED_EXCEPTION;
  }
  env.endOutput();
} // spiderMode

void clausifyMode(bool theory)
{
  CALL("clausifyMode()");

  CompositeISE simplifier;
  simplifier.addFront(new TrivialInequalitiesRemovalISE());
  simplifier.addFront(new TautologyDeletionISE());
  simplifier.addFront(new DuplicateLiteralRemovalISE());

  ScopedPtr<Problem> prb(getPreprocessedProblem());

  env.beginOutput();
  //outputSymbolDeclarations deals with sorts as well for now
  //UIHelper::outputSortDeclarations(env.out());
  UIHelper::outputSymbolDeclarations(env.out());

  ClauseIterator cit = prb->clauseIterator();
  bool printed_conjecture = false;
  while (cit.hasNext()) {
    Clause* cl = cit.next();
    cl = simplifier.simplify(cl);
    if (!cl) {
      continue;
    }
    printed_conjecture |= cl->inputType() == UnitInputType::CONJECTURE || cl->inputType() == UnitInputType::NEGATED_CONJECTURE;
    if (theory) {
      Formula* f = Formula::fromClause(cl);

      // CONJECTURE as inputType is evil, as it cannot occur multiple times
      if (cl->inference().inputType() == UnitInputType::CONJECTURE) {
        cl->inference().setInputType(UnitInputType::NEGATED_CONJECTURE);
      }

      FormulaUnit* fu = new FormulaUnit(f,cl->inference()); // we are stealing cl's inference, which is not nice!
      fu->overwriteNumber(cl->number()); // we are also making sure it's number is the same as that of the original (for Kostya from Russia to CASC, with love, and back again)
      env.out() << TPTPPrinter::toString(fu) << "\n";
    } else {
      env.out() << TPTPPrinter::toString(cl) << "\n";
    }
  }
  if(!printed_conjecture && UIHelper::haveConjecture()){
    unsigned p = env.signature->addFreshPredicate(0,"p");
    Clause* c = new(2) Clause(2,NonspecificInference0(UnitInputType::NEGATED_CONJECTURE,InferenceRule::INPUT));
    (*c)[0] = Literal::create(p,0,true,false,0);
    (*c)[1] = Literal::create(p,0,false,false,0);
    env.out() << TPTPPrinter::toString(c) << "\n";
  }
  env.endOutput();

  if (env.options->latexOutput() != "off") { outputClausesToLaTeX(prb.ptr()); }

  //we have successfully output all clauses, so we'll terminate with zero return value
  vampireReturnValue = VAMP_RESULT_STATUS_SUCCESS;
} // clausifyMode

void axiomSelectionMode()
{
  CALL("axiomSelectionMode()");

  env.options->setSineSelection(Options::SineSelection::AXIOMS);

  ScopedPtr<Problem> prb(UIHelper::getInputProblem(*env.options));

  if (prb->hasFOOL()) {
    FOOLElimination().apply(*prb);
  }

  // reorder units
  if (env.options->normalize()) {
    env.statistics->phase = Statistics::NORMALIZATION;
    Normalisation norm;
    norm.normalise(*prb);
  }

  env.statistics->phase = Statistics::SINE_SELECTION;
  SineSelector(*env.options).perform(*prb);

  env.statistics->phase = Statistics::FINALIZATION;

  UnitList::Iterator uit(prb->units());
  env.beginOutput();
  while (uit.hasNext()) {
    Unit* u = uit.next();
    env.out() << TPTPPrinter::toString(u) << "\n";
  }
  env.endOutput();

  //we have successfully output the selected units, so we'll terminate with zero return value
  vampireReturnValue = VAMP_RESULT_STATUS_SUCCESS;
}

void groundingMode()
{
  CALL("groundingMode()");

  try {
    ScopedPtr<Problem> prb(UIHelper::getInputProblem(*env.options));

    Shell::Preprocess prepro(*env.options);
    prepro.preprocess(*prb);

    ClauseIterator clauses = prb->clauseIterator();

    if (prb->hasEquality()) {
      ClauseList* eqAxioms = Grounding::getEqualityAxioms(
	      prb->getProperty()->positiveEqualityAtoms() != 0);
      clauses = pvi(
	      getConcatenatedIterator(ClauseList::DestructiveIterator(eqAxioms),
		      clauses));
    }

    MapToLIFO<Clause*, SATClause*> insts;
    Grounding gnd;
    SATClause::NamingContext nameCtx;

    while (clauses.hasNext()) {
      Clause* cl = clauses.next();
      ClauseList* grounded = gnd.ground(cl);
      SATClauseList* sGrounded = 0;
      while (grounded) {
	Clause* gcl = ClauseList::pop(grounded);
	SATClauseList::push(SATClause::fromFOClause(nameCtx, gcl), sGrounded);
      }
      insts.pushManyToKey(cl, sGrounded);
    }
    env.beginOutput();
    DIMACS::outputGroundedProblem(insts, nameCtx, env.out());
    env.endOutput();

  } catch (MemoryLimitExceededException&) {
    env.beginOutput();
    env.out() << "Memory limit exceeded\n";
    env.endOutput();
  } catch (TimeLimitExceededException&) {
    env.beginOutput();
    env.out() << "Time limit exceeded\n";
    env.endOutput();
  }
} // groundingMode

/**
 * The main function.
 * @since 03/12/2003 many changes related to logging
 *        and exception handling.
 * @since 10/09/2004, Manchester changed to use knowledge bases
 */
int main(int argc, char* argv[])
{
  CALL ("main");

  System::registerArgv0(argv[0]);
  System::setSignalHandlers();
  // create random seed for the random number generation
  Lib::Random::setSeed(123456);

  START_CHECKING_FOR_ALLOCATOR_BYPASSES;

  try {
    // read the command line and interpret it
    Shell::CommandLine cl(argc, argv);
    cl.interpret(*env.options);

    // If any of these options are set then we just need to output and exit
    if (env.options->showHelp() ||
        env.options->showOptions() ||
        env.options->showExperimentalOptions() ||
        !env.options->explainOption().empty() ||
        env.options->printAllTheoryAxioms()) {
      env.beginOutput();
      env.options->output(env.out());
      env.endOutput();
      exit(0);
    }

    //having read option reinitialize the counter
    TimeCounter::reinitialize();

    Allocator::setMemoryLimit(env.options->memoryLimit() * 1048576ul);
    Lib::Random::setSeed(env.options->randomSeed());

    switch (env.options->mode())
    {
    case Options::Mode::AXIOM_SELECTION:
      axiomSelectionMode();
      break;
    case Options::Mode::GROUNDING:
      groundingMode();
      break;
    case Options::Mode::SPIDER:
      spiderMode();
      break;
    case Options::Mode::RANDOM_STRATEGY:
      getRandomStrategy();
      break;
    case Options::Mode::CONSEQUENCE_ELIMINATION:
    case Options::Mode::VAMPIRE:
      vampireMode();
      break;

    case Options::Mode::SUBSUMPTION_TESTING:
      subsumptionTestingMode();
      break;

    case Options::Mode::SUBSUMPTION_BENCHMARK_MICRO:
      subsumptionBenchmarkMode(false);
      break;

    case Options::Mode::SUBSUMPTION_BENCHMARK_RUN:
      subsumptionBenchmarkMode(true);
      break;

    case Options::Mode::CASC:
      env.options->setIgnoreMissing(Options::IgnoreMissing::WARN);
      env.options->setSchedule(Options::Schedule::CASC);
      env.options->setOutputMode(Options::Output::SZS);
      env.options->setProof(Options::Proof::TPTP);
      env.options->setOutputAxiomNames(true);
      //env.options->setTimeLimitInSeconds(300);
      env.options->setMemoryLimit(128000);

      if (CASC::PortfolioMode::perform(env.options->slowness())) {
        vampireReturnValue = VAMP_RESULT_STATUS_SUCCESS;
      }
      break;

    case Options::Mode::CASC_HOL: {
      env.options->setIgnoreMissing(Options::IgnoreMissing::WARN);
      env.options->setSchedule(Options::Schedule::CASC_HOL_2020);
      env.options->setOutputMode(Options::Output::SZS);
      env.options->setProof(Options::Proof::TPTP);
      env.options->setMulticore(0); // use all available cores
      env.options->setOutputAxiomNames(true);
      env.options->setMemoryLimit(128000);

      unsigned int nthreads = std::thread::hardware_concurrency();
      float slowness = 1.00 + (0.04 * nthreads);

      if (CASC::PortfolioMode::perform(slowness)) {
        vampireReturnValue = VAMP_RESULT_STATUS_SUCCESS;
      }
      break;
    }
    case Options::Mode::CASC_SAT:
      env.options->setIgnoreMissing(Options::IgnoreMissing::WARN);
      env.options->setSchedule(Options::Schedule::CASC_SAT);
      env.options->setOutputMode(Options::Output::SZS);
      env.options->setProof(Options::Proof::TPTP);
      env.options->setOutputAxiomNames(true);
      //env.options->setTimeLimitInSeconds(300);
      env.options->setMemoryLimit(128000);

      if (CASC::PortfolioMode::perform(env.options->slowness())) {
        vampireReturnValue = VAMP_RESULT_STATUS_SUCCESS;
      }
      break;

    case Options::Mode::SMTCOMP:
      env.options->setIgnoreMissing(Options::IgnoreMissing::OFF);
      env.options->setInputSyntax(Options::InputSyntax::SMTLIB2);
      if(env.options->outputMode() != Options::Output::UCORE){
        env.options->setOutputMode(Options::Output::SMTCOMP);
      }
      env.options->setSchedule(Options::Schedule::SMTCOMP);
      env.options->setProof(Options::Proof::OFF);
      env.options->setMulticore(0); // use all available cores
      env.options->setTimeLimitInSeconds(1800);
      env.options->setMemoryLimit(128000);
      env.options->setStatistics(Options::Statistics::NONE);

      //TODO needed?
      // to prevent from terminating by time limit
      env.options->setTimeLimitInSeconds(100000);

      if (CASC::PortfolioMode::perform(env.options->slowness())){
        vampireReturnValue = VAMP_RESULT_STATUS_SUCCESS;
      }
      else {
        cout << "unknown" << endl;
      }
      break;

    case Options::Mode::PORTFOLIO:
      env.options->setIgnoreMissing(Options::IgnoreMissing::WARN);

      if (CASC::PortfolioMode::perform(env.options->slowness())) {
        vampireReturnValue = VAMP_RESULT_STATUS_SUCCESS;
      }
      break;

    case Options::Mode::CASC_LTB: {
      bool learning = env.options->ltbLearning()!=Options::LTBLearning::OFF;
      try {
        if(learning){
          CASC::CLTBModeLearning::perform();
        }
        else{
          CASC::CLTBMode::perform();
        }
      } catch (Lib::SystemFailException& ex) {
        cerr << "Process " << getpid() << " received SystemFailException" << endl;
        ex.cry(cerr);
        cerr << " and will now die" << endl;
      }
      //we have processed the ltb batch file, so we can return zero
      vampireReturnValue = VAMP_RESULT_STATUS_SUCCESS;
      break;
    }
    case Options::Mode::MODEL_CHECK:
      modelCheckMode();
      break;

    case Options::Mode::CLAUSIFY:
      clausifyMode(false);
      break;

    case Options::Mode::TCLAUSIFY:
      clausifyMode(true);
      break;

    case Options::Mode::OUTPUT:
      outputMode();
      break;

    case Options::Mode::PROFILE:
      profileMode();
      break;

    case Options::Mode::PREPROCESS:
    case Options::Mode::PREPROCESS2:
      preprocessMode(false);
      break;

    case Options::Mode::TPREPROCESS:
      preprocessMode(true);
      break;

    default:
      USER_ERROR("Unsupported mode");
    }
#if CHECK_LEAKS
    delete env.signature;
    env.signature = 0;
#endif
  }
#if VZ3
  catch(z3::exception& exception){
    BYPASSING_ALLOCATOR;
    vampireReturnValue = VAMP_RESULT_STATUS_UNHANDLED_EXCEPTION;
    cout << "Z3 exception:\n" << exception.msg() << endl;
    reportSpiderFail();
  }
#endif
  catch (UserErrorException& exception) {
    vampireReturnValue = VAMP_RESULT_STATUS_UNHANDLED_EXCEPTION;
    reportSpiderFail();
#if CHECK_LEAKS
    MemoryLeak::cancelReport();
#endif
    explainException(exception);
  }
catch (Parse::TPTP::ParseErrorException& exception) {
    vampireReturnValue = VAMP_RESULT_STATUS_UNHANDLED_EXCEPTION;
    reportSpiderFail();
#if CHECK_LEAKS
    MemoryLeak::cancelReport();
#endif
    explainException(exception);
  }
  catch (Exception& exception) {
    vampireReturnValue = VAMP_RESULT_STATUS_UNHANDLED_EXCEPTION;
    reportSpiderFail();
#if CHECK_LEAKS
    MemoryLeak::cancelReport();
#endif
    env.beginOutput();
    explainException(exception);
    //env.statistics->print(env.out());
    env.endOutput();
  } catch (std::bad_alloc& _) {
    vampireReturnValue = VAMP_RESULT_STATUS_UNHANDLED_EXCEPTION;
    reportSpiderFail();
#if CHECK_LEAKS
    MemoryLeak::cancelReport();
#endif
    env.beginOutput();
    env.out() << "Insufficient system memory" << '\n';
    env.endOutput();
  }
//   delete env.allocator;

  return vampireReturnValue;
} // main
