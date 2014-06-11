/**
 * @file MainLoopContext.cpp
 *
 * @since 2 Jun 2014
 * @author dmitry
 */
#include "MainLoopContext.hpp"

#include "Debug/Tracer.hpp"
#include "Kernel/ConcurrentMainLoop.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Timer.hpp"
#include "Shell/Statistics.hpp"

namespace Kernel {

using Lib::Environment;
using Lib::Timer;
using Shell::Options;
using Shell::Statistics;

	MainLoopContext::MainLoopContext(Problem& prb, const Options& opts):
			_prb(prb), _opts(opts) {

		CALL("MainLoopContext::MainLoopContext");

			_env = new Environment(*Lib::env);
	}

	MainLoopContext::~MainLoopContext() {
		CALL("MainLoopContext::~MainLoopContext");

		delete _env;
	}

	void MainLoopContext::switchIn() {
		CALL("MainLoopContext::switchIn");
		_temp_env = Lib::env;
		Lib::env = _env; //TODO: Potential change of context by other MainLoop
	}

	void MainLoopContext::switchOut() {
		CALL("MainLoopContext::switchOut");

		Lib::env = _temp_env;
	}

	void MainLoopContext::init(){
		CALL("MainLoopContext::init");

		switchIn();

		_env -> statistics -> phase = Statistics::SATURATION;
		_ml -> initAlgorithmRun();

		switchOut();
	}

	void MainLoopContext::cleanup(){
		CALL("MainLoopContext::cleanup");

		switchIn();

		_env -> statistics -> phase = Statistics::FINALIZATION;

		switchOut();
	}

	void MainLoopContext::doStep() {
		CALL("MainLoopContext::doStep");

		switchIn();
		_ml -> doOneAlgorithmStep();

		Timer::syncClock();
		if (env -> timeLimitReached()) {
			throw  TimeLimitExceededException();
		}

		switchOut();
	}
}
