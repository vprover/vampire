/**
 * @file MainLoopScheduler.cpp
 *
 * @date 7 May 2014
 * @author dmitry
 */

#include "MainLoopScheduler.hpp"
#include "MainLoop.hpp"
#include "MainLoopContext.hpp"

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

MainLoopScheduler::MainLoopScheduler(Problem& prb, OptionsList& opts) {

	  CALL("MainLoopScheduler::MainLoopScheduler");
	  ASS_G(opts.size(), 0);

	  _mlclSize = opts.size();
	  _mlcl = static_cast<MainLoopContext**>(
			  ALLOC_KNOWN(sizeof(MainLoopContext*)*_mlclSize,"MainLoopContext*"));//Lib::Array.hpp

	  OptionsList::Iterator i(opts);
	  unsigned int k = 0;
	  while(i.hasNext()){

		  Options opt = i.next();

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
			_mlcl[k] = new MainLoopContext(prb, opt);


			/*break;
		  }*/

		  k++;
	  }
	  ASS_EQ(k, _mlclSize);
}

MainLoopResult MainLoopScheduler::run() {

	CALL("MainLoopScheduler::run");

	try {

		for(unsigned int k = 0; k < _mlclSize; k++) {
			_mlcl[k] -> init();//TODO: it is assumed that timer is initialized inside. Make this consistent with time limit check.
		}

		for(;;){
			for(unsigned int k = 0; k < _mlclSize; k++) {
				_mlcl[k] -> doStep();
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
	catch(TimeLimitExceededException&) {//We catch this since SaturationAlgorithm::doUnproceessedLoop throws it
		return MainLoopResult(Statistics::TIME_LIMIT);
	}
	catch(MainLoop::MainLoopFinishedException& e) {
		return e.result;
	}
}

MainLoopScheduler::~MainLoopScheduler() {

	CALL("MainLoopScheduler::~MainLoopScheduler");

	for(unsigned int k = 0; k < _mlclSize; k++) {
		delete _mlcl[k]; //TODO: should be DEALLOC_UNKNOWN but SaturationAlgorithm::createFromOptions allocates via "new"
	}
	DEALLOC_KNOWN(_mlcl, sizeof(MainLoopContext*)*_mlclSize, "ConcurrentMainLoop*");
}

/*static MainLoopScheduler* MainLoopScheduler::createFromOptions(Problem& prb, OptionsList* opts) {

	CALL("MainLoopScheduler::createFromOptions");
	return new MainLoopScheduler(prb, opts);

}*/
