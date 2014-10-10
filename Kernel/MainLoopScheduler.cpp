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

MainLoopScheduler::MainLoopScheduler(Problem& prb, size_t capacity): _prb(prb), _capacity(capacity) {
	  CALL("MainLoopScheduler::MainLoopScheduler");
	  //_mlclSize = opts.size();

	  ASS_G(_capacity, 0);

	// Check that this constructor has not previously been run i.e. we are a singleton
//	  ASS(!_mlcl);

	  _mlcl = static_cast<MainLoopContext**>(
	  		  ALLOC_KNOWN(sizeof(MainLoopContext*)*_capacity,"MainLoopContext*"));

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

MainLoopScheduler::MainLoopScheduler(Problem& prb, std::size_t capacity, OptionsList& opts):
		_prb(prb), _capacity(capacity) {
	CALL("MainLoopScheduler::MainLoopScheduler");
	//MainLoopScheduler::MainLoopScheduler(prb, capacity){
	ASS_G(_capacity, 0);
//	ASS(!_mlcl);

    _mlcl = static_cast<MainLoopContext**>(
		  		  ALLOC_KNOWN(sizeof(MainLoopContext*)*_capacity,"MainLoopContext*"));

	addStrategies(opts);
}

MainLoopScheduler::MainLoopScheduler(Problem& prb, OptionsList& opts):
		_prb(prb), _capacity(opts.size()) {
	CALL("MainLoopScheduler::MainLoopScheduler");
		//MainLoopScheduler::MainLoopScheduler(prb, opts.size(), opts) {
	ASS_G(_capacity, 0);
//	ASS(!_mlcl);

    _mlcl = static_cast<MainLoopContext**>(
		  		  ALLOC_KNOWN(sizeof(MainLoopContext*)*_capacity,"MainLoopContext*"));

    addStrategies(opts);
}

MainLoopResult MainLoopScheduler::run() {

	CALL("MainLoopScheduler::run");

	MainLoopResult* result = 0;
	try {

		/*for(size_t k = 0; k < _mlclSize; k++) {
			//_currentContext = _mlcl[k];
//#if VDEBUG
//			cout << "initialising context " << k << endl;
//			cout << "isInitialised()? " << _mlcl[k] -> isInitialised() << endl;
//#endif
			_mlcl[k] -> init();
		}
//#if VDEBUG
//		cout << "all context are initialised" << endl;
//#endif
		*/
		size_t live_strategies = 0;
		while(!result){
			for(size_t k = 0; k < _capacity; k++) {

				cout << "Working with " << k << endl;

				// TODO - add local timers and stop a strategy if it uses up all of its time (need an option for this)
				try{
					if(_mlcl[k]){
						_mlcl[k] -> doStep();
					}else{
						cout << "Empty " << k << endl;
						if(!optionsQueue.empty()){
							cout << "Creating " << k << endl;
							_mlcl[k] = createContext(_prb, const_cast<Options&>(optionsQueue.top()));
							ASS(_mlcl[k]);
							optionsQueue.pop();
							live_strategies++;
							_mlcl[k] -> doStep();
						}
					}
				}catch(LocalTimeLimitExceededException&) {
#if VDEBUG
					cout << "Killing " << _mlcl[k] -> _id << " as local time limit exceeded" << endl;
#endif //VDEBUG
					delete _mlcl[k];
					_mlcl[k] = 0;
					live_strategies--;
					//check if there are any strategies left
					if(live_strategies==0 && optionsQueue.empty()){
						result = new MainLoopResult(Statistics::LOCAL_TIME_LIMIT);
						break;
					}
				}catch(MainLoop::MainLoopFinishedException& e) {
#if VDEBUG
					cout << "Strategy " << _mlcl[k] -> _id << " found result" << endl;
#endif //VDEBUG
					if(e.result.terminationReason == Statistics::SATISFIABLE){
						result =  &e.result;
						break;
					}
					// remove strategy!
					delete _mlcl[k];
					_mlcl[k]=0;
					live_strategies--;

					//check if there are any strategies left
					if(live_strategies==0 && optionsQueue.empty()){
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

/*	// do cleanup
	Lib::Timer::setTimeLimitEnforcement(false);
	for(size_t k = 0; k < _mlclSize; k++) {
		if(_mlcl[k]){_mlcl[k] -> cleanup();}
	}
*/

	result -> updateStatistics();

	return *result;
}

MainLoopScheduler::~MainLoopScheduler() {

	CALL("MainLoopScheduler::~MainLoopScheduler()");

	for(size_t k = 0; k < _capacity; k++) {
		if(_mlcl[k]){
			delete _mlcl[k]; //TODO: should be DEALLOC_UNKNOWN but SaturationAlgorithm::createFromOptions allocates via "new"
		}
	}

	DEALLOC_KNOWN(_mlcl, sizeof(MainLoopContext*)*_capacity, "MainLoopContext*");
}

}
