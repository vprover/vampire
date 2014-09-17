/**
 * @file MainLoopContext.cpp
 *
 * @since 2 Jun 2014
 * @author dmitry
 */
#include "MainLoopContext.hpp"

#include "Debug/Tracer.hpp"
#include "Kernel/ConcurrentMainLoop.hpp"
#include "Kernel/Problem.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Timer.hpp"
#include "Shell/Statistics.hpp"

namespace Kernel {

using Lib::Environment;
using Lib::Timer;
using Shell::Options;
using Shell::Statistics;

unsigned MainLoopContext::id_counter=0;

MainLoopContext* MainLoopContext::currentContext = 0;

	MainLoopContext::MainLoopContext(Problem& prb, Options& opts):
#if VDEBUG
			_id(id_counter++),
#endif
                        _opts(opts), _startTime(0), _elapsed(0) {

		CALL("MainLoopContext::MainLoopContext");


                // We must copy the problem otherwise we share clauses
                // This is an issue as clauses store information about
                // how they are used in a proof attempt
                _prb = prb.copy(true);

		//TODO - why do we need to store prb and opts if they will be in env?
		_env = new Environment(*Lib::env,opts);
	}

	MainLoopContext::~MainLoopContext() {
		CALL("MainLoopContext::~MainLoopContext");
		delete _env;
		delete _prb;
//		switchOut();
	}


	void MainLoopContext::switchIn() {
		CALL("MainLoopContext::switchIn");
		_temp_env = Lib::env;
		Lib::env = _env; //TODO: Potential change of context by other MainLoop
		_startTime = _env -> timer-> elapsedMilliseconds();
#if VDEBUG
		std::cout << "Switching in: local time limit: " << _env->options->localTimeLimitInDeciseconds() <<
				" dsec, elapsed so far: " << _elapsed << " msec" <<
				std::endl;
#endif //VDEBUG
		currentContext = this;
	}

	void MainLoopContext::switchOut() {
		CALL("MainLoopContext::switchOut");

	    const unsigned int endTime = _env -> timer -> elapsedMilliseconds();

		ASS_GE(endTime,_startTime);

		_elapsed += (endTime - _startTime);
#if VDEBUG
		std::cout << "Switching out: local time limit: " << _env->options->localTimeLimitInDeciseconds() <<
				" dsec, elapsed so far: " << _elapsed << " msec" <<
				std::endl;
#endif //VDEBUG
		Lib::env = _temp_env;
		currentContext = 0;
	}

	void MainLoopContext::init(){
		CALL("MainLoopContext::init");

		AutoSwitch s(this);

		_env -> statistics -> phase = Statistics::SATURATION;
		_ml -> initAlgorithmRun();
	}

	void MainLoopContext::cleanup(){
		CALL("MainLoopContext::cleanup");

		AutoSwitch s(this);
		_env -> statistics -> phase = Statistics::FINALIZATION;
	}

	void MainLoopContext::doStep() {
		CALL("MainLoopContext::doStep");

		AutoSwitch s(this);
		_ml -> doOneAlgorithmStep();
		_env -> checkAllTimeLimits();
	}

	unsigned int MainLoopContext::updateTimeCounter() {
		const unsigned int endTime = _env->timer->elapsedMilliseconds();
		ASS_GE(endTime,_startTime);
		_elapsed += (endTime - _startTime);
		_startTime = endTime;
		return _elapsed; //return in milliseconds
	}
}
