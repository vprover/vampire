/**
 * @file MainLoopContext.hpp
 *
 * @date 19 May 2014
 * @author dmitry
 */

#ifndef __MainLoopContext__
#define __MainLoopContext__

#include "Kernel/Problem.hpp"
#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Timer.hpp"

namespace Kernel {

using namespace Lib;
using namespace Shell;
using namespace Saturation;

class MainLoopContext {
public:
	MainLoopContext(Problem& prb, Options& opt): _prb(prb), _opt(opt) {
		CALL("MainLoopContext::MainLoopContext(Problem&, Options&)");

		if(Lib::env) {
			_env = new Environment(*Lib::env);
		}else{
			_env = new Environment();
		}

		init();
	}

	virtual ~MainLoopContext() {
		CALL("MainLoopContext::~MainLoopContext()");

		cleanUp();
		delete _env;
	}

	virtual void init() {
		CALL("MainLoopContext::init()");

		switchIn();

		_ml = SaturationAlgorithm::createFromOptions(_prb, _opt);

		_ml -> initAlgorithmRun();

		switchOut();
	}

	virtual void cleanUp() {
		CALL("MainLoopContext::cleanUp()");

		delete _ml;
	}

	virtual void doStep() {
		CALL("MainLoopContext::doStep()");

		switchIn();
		_ml -> doOneAlgorithmStep();

		Timer::syncClock();
		if (env -> timeLimitReached()) {
			throw  TimeLimitExceededException();
		}

		switchOut();
	}

	virtual void switchIn() {
		CALL("MainLoopContext::switchIn()");

		Lib::env = _env; //TODO: Potential change of context by other MainLoop
	}

	virtual void switchOut() {
		CALL("MainLoopContext::switchOut()");

		_env = Lib::env;
	}

private:
	Problem& _prb;
	ConcurrentMainLoop* _ml;
	Environment* _env;
	Options& _opt;

/*	static void copy(Environment& to, Environment& from){
		to.colorUsed = from.colorUsed;
		to.options = from.options;
		to.ordering = from.ordering;
		to.property = from.property;
		to.

	}
*/
};

} /* namespace Kernel */

#endif /* __MainLoopContext__ */
