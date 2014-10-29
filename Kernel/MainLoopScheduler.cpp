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
#include "Kernel/Problem.hpp"

namespace Kernel {

using std::size_t;

using InstGen::IGAlgorithmContext;

using Saturation::SaturationAlgorithmContext;
using Shell::Options;
using Shell::OptionsList;
using Shell::Preprocess;

//MainLoopContext* MainLoopScheduler::_currentContext = 0;
//MainLoopContext** MainLoopScheduler::_mlcl = 0;
//size_t MainLoopScheduler::_capacity = 0;

MainLoopContext* MainLoopScheduler::createContext(Problem& prb, Options& opt) {
	CALL("MainLoopScheduler::createContext");

	switch (opt.saturationAlgorithm()) {
	  case Options::INST_GEN:
		return new IGAlgorithmContext(prb, opt);
		break;
	  default:
		return new SaturationAlgorithmContext(prb, opt);
	}
}

MainLoopScheduler::MainLoopScheduler(Problem& prb, size_t capacity):
		_prb(prb), _capacity(capacity), _contextCounter(0), _maxTimeSlice(0) {
	  CALL("MainLoopScheduler::MainLoopScheduler");
	  //_mlclSize = opts.size();

	  ASS_G(_capacity, 0);

	// Check that this constructor has not previously been run i.e. we are a singleton
//	  ASS(!_mlcl);

	  _mlcl = static_cast<MainLoopContext**>(
	  		  ALLOC_KNOWN(sizeof(MainLoopContext*)*_capacity,"MainLoopContext*"));
	  for(size_t k = 0; k < _capacity; k++) _mlcl[k] = 0;


/*	  OptionsList::Iterator i(opts);
	  size_t k = 0;
	  while(i.hasNext()){

		  Options& opt = i.next();
#if VDEBUG
		  cout << "Creating strategy " << k << " with " << opt.localTimeLimitInDeciseconds() << " and " << opt.timeLimitInDeciseconds() << " local and global time" << endl;
#endif//VDEBUG

		  _mlcl[k] = createContext(prb, opt);
		  k++;
	  }
	  ASS_EQ(k, _mlclSize);
*/
}

MainLoopScheduler::MainLoopScheduler(Problem& prb, OptionsList& opts,
		std::size_t capacity):
		_prb(prb), _capacity(capacity), _contextCounter(0), _maxTimeSlice(0) {
	CALL("MainLoopScheduler::MainLoopScheduler");
	//MainLoopScheduler::MainLoopScheduler(prb, capacity){
	ASS_G(_capacity, 0);
//	ASS(!_mlcl);

    _mlcl = static_cast<MainLoopContext**>(
		  		  ALLOC_KNOWN(sizeof(MainLoopContext*)*_capacity,"MainLoopContext*"));
    for(size_t k = 0; k < _capacity; k++) _mlcl[k] = 0;

	addStrategies(opts);
}

MainLoopScheduler::MainLoopScheduler(Problem& prb, OptionsList& opts):
		_prb(prb), _capacity(opts.size()), _contextCounter(0), _maxTimeSlice(0) {
	CALL("MainLoopScheduler::MainLoopScheduler");
		//MainLoopScheduler::MainLoopScheduler(prb, opts.size(), opts) {
	ASS_G(_capacity, 0);
//	ASS(!_mlcl);

    _mlcl = static_cast<MainLoopContext**>(
		  		  ALLOC_KNOWN(sizeof(MainLoopContext*)*_capacity,"MainLoopContext*"));
    for(size_t k = 0; k < _capacity; k++) _mlcl[k] = 0;

    addStrategies(opts);
}

MainLoopResult MainLoopScheduler::run() {

	CALL("MainLoopScheduler::run");

        cout << "Beginning run with " << _capacity << " concurrent strategies." << endl;

	MainLoopResult* result = 0;
	try {

		while(!result){
			for(size_t k = 0; k < _capacity; k++) {
				try{
					if(_mlcl[k]){
						contextStep(k);
					}else{
						if(!optionsQueue.empty()){
							addContext(k);
							contextStep(k);
						}
					}
				}catch(LocalTimeLimitExceededException&) {
#if VDEBUG
					cout << "Killing " << _mlcl[k] -> _id << " as local time limit exceeded" << endl;
#endif //VDEBUG
					deleteContext(k);
					//check if there are any strategies left
					if(exausted()){
						result = new MainLoopResult(Statistics::LOCAL_TIME_LIMIT);
						break;
					}
				}catch(MainLoop::MainLoopFinishedException& e) {
#if VDEBUG
					cout << "Strategy " << _mlcl[k] -> _id << " found result" << endl;
#endif //VDEBUG
					deleteContext(k);
					if( (e.result.terminationReason == Statistics::SATISFIABLE) ||
							exausted()){
						result =  &e.result;
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
	Lib::Timer::setTimeLimitEnforcement(false);
	result -> updateStatistics();

	return *result;
}

MainLoopScheduler::~MainLoopScheduler() {

	CALL("MainLoopScheduler::~MainLoopScheduler()");

#if VDEBUG
		cout << "Deleting scheduler" << endl;
#endif //VDEBUG

	for(size_t k = 0; k < _capacity; k++) {
		if(_mlcl[k]){
			delete _mlcl[k]; //TODO: should be DEALLOC_UNKNOWN but SaturationAlgorithm::createFromOptions allocates via "new"
		}
	}

	DEALLOC_KNOWN(_mlcl, sizeof(MainLoopContext*)*_capacity, "MainLoopContext*");
}

}
