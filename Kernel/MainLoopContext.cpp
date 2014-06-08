/**
 * @file MainLoopContext.cpp
 *
 * @since 2 Jun 2014
 * @author dmitry
 */
#include "MainLoopContext.hpp"

#include "Debug/Tracer.hpp"
#include "Lib/Environment.hpp"

namespace Kernel {

using Lib::Environment;
using Shell::Options;

	MainLoopContext::MainLoopContext(Problem& prb, const Options& opt):
			_prb(prb), _opt(opt) {

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

}
