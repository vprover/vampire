/*
 * InvariantHelper.cpp
 *      Location: Vienna
 */

#include "InvariantHelper.hpp"

#include "Debug/Tracer.hpp"

#include "Lib/DArray.hpp"
#include "Lib/Int.hpp"
#include "Lib/Environment.hpp"
#include "Lib/TimeCounter.hpp"
#include "Lib/Timer.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/ScopedPtr.hpp"

#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/Problem.hpp"

#include "Api/FormulaBuilder.hpp"
#include "Api/Problem.hpp"

#include "Saturation/ProvingHelper.hpp"

#include "Shell/Options.hpp"
#include "Shell/Property.hpp"
#include "Shell/Preprocess.hpp"
#include "Shell/UIHelper.hpp"
#include "Shell/SpecialTermElimination.hpp"
#include "Shell/TheoryFinder.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/InterpretedNormalizer.hpp"
#include "Shell/TheoryAxioms.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

using namespace Kernel;
using namespace Program;
using namespace Shell;
using namespace Saturation;

namespace Program
{
  InvariantHelper::~InvariantHelper(){}
void InvariantHelper::setSEIOptions(int timeLimit)
{
  CALL("InvariantHelper::setSEIOptions");

  env.options->set("splitting", "off");
  env.options->set("show_symbol_elimination", "on");
  env.options->set("unused_predicate_definition_removal", "off");
  env.options->set("propositional_to_bdd","off");

  if (env.options->timeLimitInDeciseconds() == 0)
    env.options->set("time_limit", "10");

  env.options->setNaming(32000);
}

void InvariantHelper::preprocessUnits(Problem& prb)
{
  CALL("InvariantHelper::preprocessUnits");

  Preprocess p(*env.options);
  p.preprocess(prb);
}

void InvariantHelper::runVampireSaturationN(Problem& prb){
  CALL("InvariantHelper::runVampireSaturationN");
  try{
    Unit::onPreprocessingEnd();

    TRACE("preproc_forms",
        env.beginOutput();
        UIHelper::outputAllPremises(cout, prb.units(), "New: ");
        env.endOutput();
    );

    env.statistics->phase=Statistics::SATURATION;
    ScopedPtr<MainLoop> salg(MainLoop::createFromOptions(prb, *env.options));
    MainLoopResult sres(salg->run());
    env.statistics->phase=Statistics::FINALIZATION;
    Timer::setTimeLimitEnforcement(false);
    sres.updateStatistics();
  }
  catch(MemoryLimitExceededException&){
    env.statistics->terminationReason=Statistics::MEMORY_LIMIT;
       env.statistics->refutation=0;
       size_t limit=Allocator::getMemoryLimit();
       //add extra 1 MB to allow proper termination
       Allocator::setMemoryLimit(limit+1000000);
  }
  catch(TimeLimitExceededException&){
    cout<<"time limit exception"<<endl;
    env.statistics->terminationReason=Statistics::TIME_LIMIT;
        env.statistics->refutation=0;
  }
}
Problem* InvariantHelper::preprocessUnits()
{
  CALL("InvariantHelper::preprocessUnits/1");

  Problem* prb = new Problem(_units);
  Preprocess p(*env.options);
  p.preprocess(*prb);
  p.preprocess1(*prb);
  return prb;

}
void InvariantHelper::runSEI()
{
  CALL("InvariantHelper::runSEI");
  Problem* prb = new Problem(_units);
  preprocessUnits(*prb);

  TRACE("preproc_forms",
            env.beginOutput();
            UIHelper::outputAllPremises(tout, (*prb).units(), "New: ");
            UIHelper::outputIntroducedSymbolDeclarations(tout);
            env.endOutput();
        );
  setSEIOptions(_timeLimit);

#if false
  Problem* prb = preprocessUnits();
  showSignature();
#endif
#if true
   //ProvingHelper::runVampireSaturationN(*prb,*env.options);
  runVampireSaturationN(*prb);
#else
  ProvingHelper::runVampire(*prb, *env.options);
#endif

}

void InvariantHelper::showSignature()
{
  CALL("InvariantHelper::showSignature");
  for (unsigned int i = 0; i < env.signature->functions(); i++)
    cout << env.signature->getFunction(i)->name() << " "
	    << (env.signature->getFunction(i)->color() == COLOR_LEFT ? " left "
		    : " other ") << env.signature->getFunction(i)->arity()
	    << endl;

  for (unsigned int i = 0; i < env.signature->predicates(); i++)
    cout << env.signature->getPredicate(i)->name() << " "
	    << (env.signature->getPredicate(i)->color() == COLOR_LEFT ? " left "
		    : " other") << env.signature->getPredicate(i)->arity()
	    << endl;

}

void InvariantHelper::showPreprocUnits(Problem *prb)
{
  CALL("InvariantHelper::showPreprocUnits");

  UnitList::Iterator ite(prb->units());
  while (ite.hasNext()) {
    cout << ite.next()->toString() << endl;
  }
}

void InvariantHelper::run()
{
  CALL("InvariantHelper::run");

  runSEI();
}

}
