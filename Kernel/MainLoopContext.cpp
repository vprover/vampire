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

	MainLoopContext::MainLoopContext(Problem& prb, Options& opts):
			_opts(opts), _startTime(0), _endTime(0), _elapsedDeciseconds(0) {

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
		_startTime = _env -> timer-> elapsedDeciseconds();
	}

	void MainLoopContext::switchOut() {
		CALL("MainLoopContext::switchOut");

		_endTime = _env -> timer -> elapsedDeciseconds();
		_elapsedDeciseconds += (_endTime - _startTime);
		Lib::env = _temp_env;
	}

	void MainLoopContext::init(){
		CALL("MainLoopContext::init");

		AutoSwitch(this);

		_env -> statistics -> phase = Statistics::SATURATION;
		_ml -> initAlgorithmRun();
	}

	void MainLoopContext::cleanup(){
		CALL("MainLoopContext::cleanup");

		AutoSwitch(this);
		_env -> statistics -> phase = Statistics::FINALIZATION;
	}

	void MainLoopContext::doStep() {
		CALL("MainLoopContext::doStep");

		AutoSwitch(this);
		_ml -> doOneAlgorithmStep();
		env -> checkAllTimeLimits();
	}
}
