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

#if VDEBUG
unsigned int MainLoopContext::id_counter = 0;
#endif //VDEBUG

MainLoopContext* MainLoopContext::currentContext = 0;

	MainLoopContext::MainLoopContext(Problem& prb, Options& opts):
#if VDEBUG
			_id(id_counter++),
#endif
            _opts(opts), _startTime(0), _elapsed(0), _initialised(false), _steps(0) {

		CALL("MainLoopContext::MainLoopContext");

#if VDEBUG
		cout << "Creating context " << _id << " with " << opts.localTimeLimitInDeciseconds() <<
				" and " << opts.timeLimitInDeciseconds() << " local and global time" << endl;
#endif//VDEBUG

		// We must copy the problem otherwise we share clauses
		// This is an issue as clauses store information about
		// how they are used in a proof attempt
		_prb = prb.copy(true);

		//TODO - why do we need to store prb and opts if they will be in env?
		_env = new Environment(*Lib::env,opts);
	}

	MainLoopContext::~MainLoopContext() {
		CALL("MainLoopContext::~MainLoopContext");

		if(_initialised) cleanup();

#if VDEBUG
		cout << "Deleting context " <<  _id << endl;
#endif //VDEBUG

                ASS(_env); ASS(_prb);
		delete _env;
		delete _prb;
	}


	void MainLoopContext::switchIn() {
		CALL("MainLoopContext::switchIn");
		_temp_env = Lib::env;
		Lib::env = _env;
		_startTime = _env -> timer-> elapsedMilliseconds();
#if VDEBUG
		std::cout << "Switching in " << _id << ". Local time limit: " << _env->options->localTimeLimitInDeciseconds() <<
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
		std::cout << "Switching out " << _id << ". Local time limit: " << _env->options->localTimeLimitInDeciseconds() <<
				" dsec, elapsed so far: " << _elapsed << " msec" <<
				std::endl;
#endif //VDEBUG
		Lib::env = _temp_env;
		currentContext = 0;
	}

	void MainLoopContext::init(){
		CALL("MainLoopContext::init");

		ASS(!_initialised);

#if VDEBUG
		cout << "Initialising context " <<  _id << endl;
#endif //VDEBUG

		AutoSwitch s(this);
		_env -> statistics -> phase = Statistics::SATURATION;
		_ml -> initAlgorithmRun();
		_initialised = true;
	}

	void MainLoopContext::cleanup(){
		CALL("MainLoopContext::cleanup");

#if VDEBUG
		cout << "Cleaning up context " <<  _id << endl;
#endif //VDEBUG

		AutoSwitch s(this);
		_env -> statistics -> phase = Statistics::FINALIZATION;
		_initialised = false;
	}

	void MainLoopContext::doStep(unsigned int timeSlice) {
		CALL("MainLoopContext::doStep");

		const int end = _env -> timer -> elapsedMilliseconds() + timeSlice;

		if(!_initialised) init(); //Lazy initialisation in order to work with huge number of contexts

#if VDEBUG
		cout << "Doing steps in context " <<  _id << " within time slice " << timeSlice << " msec" << endl;
#endif //VDEBUG

		AutoSwitch s(this);
		do{//ensures at least one step
			_ml -> doOneAlgorithmStep();

#if VDEBUG
		cout << "Finished step " << _steps << " in context " <<  _id << endl;
#endif //VDEBUG

			_steps++;
			_env -> checkAllTimeLimits();
		}while(_env -> timer -> elapsedMilliseconds() < end);
#if VDEBUG
		cout << "Average time " << averageTimeSlice() << " msec per step" << endl;
#endif //VDEBUG

	}

	unsigned int MainLoopContext::updateTimeCounter() {
		const unsigned int endTime = _env->timer->elapsedMilliseconds();
		ASS_GE(endTime,_startTime);
		_elapsed += (endTime - _startTime);
		_startTime = endTime;
		return _elapsed; //return in milliseconds
	}
}
