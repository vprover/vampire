/**
 * @file MainLoopScheduler.cpp
 *
 * @since 7 May 2014
 * @author dmitry
 */

#include "MainLoopScheduler.hpp"

#include "Kernel/MainLoop.hpp"
#include "Kernel/MainLoopContext.hpp"
#include "Lib/Timer.hpp"
#include "InstGen/IGAlgorithmContext.hpp"
#include "Saturation/SaturationAlgorithmContext.hpp"
#include "Shell/OptionsList.hpp"
#include "Shell/Preprocess.hpp"

namespace Kernel {

using std::size_t;

using InstGen::IGAlgorithmContext;

using Saturation::SaturationAlgorithmContext;
using Shell::Options;
using Shell::OptionsList;
using Shell::Preprocess;

MainLoopScheduler::MainLoopScheduler(Problem& prb, OptionsList& opts) {

	  CALL("MainLoopScheduler::MainLoopScheduler");
	  _mlclSize = opts.size();

	  ASS_G(_mlclSize, 0);

	  _mlcl = static_cast<MainLoopContext**>(
	  		  ALLOC_KNOWN(sizeof(MainLoopContext*)*_mlclSize,"MainLoopContext*"));

	// Do preprocessing
	// This is (currently) global for all strategies
	{
		TimeCounter tc(TC_PREPROCESSING);
		//TODO : make this nicer, should probably just use opt in env already
		// use first option as they should share the preprocessing options
		OptionsList::Iterator i(opts);
		ASS(i.hasNext());
		Preprocess prepro(i.next());
		prepro.preprocess(prb);
	}

	  OptionsList::Iterator i(opts);
	  size_t k = 0;
	  while(i.hasNext()){

		  Options& opt = i.next();

		  /*if(opt.bfnt()) {
			_mla[k] = new BFNTMainLoop(prb, opt);
		  }*/

		  switch (opt.saturationAlgorithm()) {
		  /*case Options::TABULATION:
			_mla[k] = new TabulationAlgorithm(prb, opt);
			break;*/
		  case Options::INST_GEN:
			_mlcl[k] = new IGAlgorithmContext(prb, opt);
			break;
		  default:
			_mlcl[k] = new SaturationAlgorithmContext(prb, opt);
			break;
		  }

		  k++;
	  }
	  ASS_EQ(k, _mlclSize);
}

MainLoopResult MainLoopScheduler::run() {

	CALL("MainLoopScheduler::run");


	MainLoopResult* result = 0;
	try {

		for(size_t k = 0; k < _mlclSize; k++) {
			_mlcl[k] -> init();
		}

		size_t live_strategies = _mlclSize;
		while(!result){
			for(size_t k = 0; k < _mlclSize; k++) {
				// TODO - add local timers and stop a strategy if it uses up all of its time (need an option for this)
				try{
					if(_mlcl[k]){
						_mlcl[k] -> doStep();
					}
				}catch(LocalTimeLimitExceededException&) {
					delete _mlcl[k];
					_mlcl[k] = 0;
					live_strategies--;
					//check if there are any strategies left
					if(live_strategies==0){
						result = new MainLoopResult(Statistics::LOCAL_TIME_LIMIT);
						break;
					}
				}catch(MainLoop::MainLoopFinishedException& e) {
					if(e.result.terminationReason == Statistics::SATISFIABLE){
						result =  &e.result;
						break;
					}
					// remove strategy!
					delete _mlcl[k];
					_mlcl[k]=0;
					live_strategies--;

					//check if there are any strategies left
					if(live_strategies==0){
						result = &e.result;
						break;
					}
				}
			}
		}
		//Should only be here if result set
	}catch(MainLoop::RefutationFoundException& rs) {
		result = new MainLoopResult(Statistics::REFUTATION, rs.refutation);
	}
	catch(TimeLimitExceededException&) {//We catch this since SaturationAlgorithm::doUnproceessedLoop throws it
		result = new MainLoopResult(Statistics::TIME_LIMIT);
	}
	catch(MemoryLimitExceededException&) {
		env -> statistics->refutation=0;
		size_t limit=Allocator::getMemoryLimit();
		//add extra 1 MB to allow proper termination
		Allocator::setMemoryLimit(limit+1000000);
		result = new MainLoopResult(Statistics::MEMORY_LIMIT);
	}

	ASS(result);

	// do cleanup
	Lib::Timer::setTimeLimitEnforcement(false);
	for(size_t k = 0; k < _mlclSize; k++) {
		_mlcl[k] -> cleanup();
	}
	result -> updateStatistics();

	return *result;

}

MainLoopScheduler::~MainLoopScheduler() {

	CALL("MainLoopScheduler::~MainLoopScheduler()");

	for(size_t k = 0; k < _mlclSize; k++) {
		if(_mlcl[k]){
			delete _mlcl[k]; //TODO: should be DEALLOC_UNKNOWN but SaturationAlgorithm::createFromOptions allocates via "new"
		}
	}
	DEALLOC_KNOWN(_mlcl, sizeof(MainLoopContext*)*_mlclSize, "MainLoopScheduler");
}

}
