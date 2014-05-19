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

namespace Kernel {

using namespace Lib;
using namespace Shell;
using namespace Saturation;

class MainLoopContext {
public:
	MainLoopContext(Problem& prb, Options& opt): _prb(prb), _opt(opt) {

		//_env = new Environment();

		init();
	}

	virtual ~MainLoopContext() {

		delete _ml;
		//delete _env;
	}

	virtual void init() {
		CALL("MainLoopContext::init");

		switchIn();

		_ml = SaturationAlgorithm::createFromOptions(_prb, _opt);

		_ml -> initAlgorithmRun();

		switchOut();
	}

	virtual void doStep() {
		CALL("MainLoopContext::doStep");

		switchIn();
		_ml -> doOneAlgorithmStep();
		switchOut();
	}

	virtual void switchIn() {
		CALL("MainLoopContext::switchContext");

		Lib::env = _env; //TODO: Potential change of context by other MainLoop
	}

	virtual void switchOut() {
		CALL("MainLoopContext::saveContext");

		_env = Lib::env;
	}

private:
	Problem& _prb;
	ConcurrentMainLoop* _ml;
	Environment _env;
	Options& _opt;
};

} /* namespace Kernel */

#endif /* __MainLoopContext__ */
