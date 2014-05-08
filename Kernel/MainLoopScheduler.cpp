/**
 * @file MainLoopScheduler.cpp
 *
 * @date 7 May 2014
 * @author dmitry
 */

#include "MainLoopScheduler.hpp"
#include "MainLoop.hpp"

#include "Lib/Allocator.hpp"
#include "Lib/Timer.hpp"

//#include "InstGen/IGAlgorithm.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

//#include "Tabulation/TabulationAlgorithm.hpp"

//#include "Shell/BFNTMainLoop.hpp"
#include "Shell/Options.hpp"

using namespace Kernel;
using namespace Shell;
//using namespace InstGen;
using namespace Saturation;
//using namespace Tabulation;

MainLoopScheduler::MainLoopScheduler(Problem& prb, OptionsList* opts): _prb(prb), _opts(opts) {

	  CALL("MainLoopScheduler::MainLoopScheduler");
	  ASS_G(opts -> length(), 0);

	  _mlaSize = opts -> length();
	  _mla = static_cast<ConcurrentMainLoop**>(
			  ALLOC_KNOWN(sizeof(ConcurrentMainLoop*)*_mlaSize,"ConcurrentMainLoop*"));

	  OptionsList::Iterator i(opts);
	  unsigned int k = 0;
	  while(i.hasNext()){

		  //Options *opt = i.next();

		  /*if(opt.bfnt()) {
			_mla[k] = new BFNTMainLoop(prb, opt);
		  }

		  switch (opt.saturationAlgorithm()) {
		  case Options::TABULATION:
			_mla[k] = new TabulationAlgorithm(prb, opt);
			break;
		  case Options::INST_GEN:
			_mla[k] = new IGAlgorithm(prb, opt);
			break;
		  default:*/
			_mla[k] = SaturationAlgorithm::createFromOptions(prb, *i.next());
			/*break;
		  }*/

		  k++;
	  }
	  ASS_EQ(k, _mlaSize);
}

MainLoopResult MainLoopScheduler::run() {

	CALL("MainLoopScheduler::run");

	try {

		for(unsigned int k = 0; k < _mlaSize; k++) {
			_mla[k] -> initAlgorithmRun();//TODO: it is assumed that timer is initialized inside. Make this consistent with time limit check.
		}

		for(;;){
			for(unsigned int k = 0; k < _mlaSize; k++) {
				_mla[k] -> doOneAlgorithmStep();
				Timer::syncClock();
				if (env.timeLimitReached()) {
					return MainLoopResult(Statistics::TIME_LIMIT);
				}
			}
		}
		//Should never be here
	}
	catch(MainLoop::RefutationFoundException& rs) {
		return MainLoopResult(Statistics::REFUTATION, rs.refutation);
	}
	/*catch(TimeLimitExceededException&) {
		return MainLoopResult(Statistics::TIME_LIMIT);
	}*/
	catch(MainLoop::MainLoopFinishedException& e) {
		return e.result;
	}
}

MainLoopScheduler::~MainLoopScheduler() {

	CALL("MainLoopScheduler::~MainLoopScheduler");

	for(unsigned int k = 0; k < _mlaSize; k++) {
		delete _mla[k]; //TODO: should be DEALLOC_UNKNOWN but SaturationAlgorithm::createFromOptions allocates via "new"
	}
	DEALLOC_KNOWN(_mla, sizeof(ConcurrentMainLoop*)*_mlaSize, "ConcurrentMainLoop*");
}

/*static MainLoopScheduler* MainLoopScheduler::createFromOptions(Problem& prb, OptionsList* opts) {

	CALL("MainLoopScheduler::createFromOptions");
	return new MainLoopScheduler(prb, opts);

}*/
