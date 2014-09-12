/**
 * @file MainLoopContext.hpp
 *
 * @since 19 May 2014
 * @author dmitry
 */

#ifndef __MainLoopContext__
#define __MainLoopContext__

#include "Lib/EnvironmentFwd.hpp"
#include "Kernel/ConcurrentMainLoopFwd.hpp"
#include "Kernel/ProblemFwd.hpp"
#include "Shell/OptionsFwd.hpp"

namespace Kernel {


class MainLoopContext {
public:
	MainLoopContext(Problem& prb, Shell::Options& opts);

	virtual ~MainLoopContext();

	// Do one main loop step in this context
	virtual void doStep();
	// Do init required by algorithm, and set phase
	virtual void init();
	// Do cleanup required by algorithm, and set phase
	virtual void cleanup();

	// Get the ConcurrentMainLoop
	ConcurrentMainLoop* getMainLoop() const { return _ml; }

	int updateTimeCounter();
	int elapsedDeciseconds() const {
		return _elapsed / 100;
	}
	int elapsed() const {
		return _elapsed;
	}

#if VDEBUG
	bool checkEnvironment(const Lib::Environment* env) const {
		return (_env == env);
	}
#endif //VDEBUG

	static MainLoopContext* currentContext;

protected:
	// Switch into this context
	void switchIn();
	// Switch out from the context
	void switchOut();

	class AutoSwitch{
		public:
	        AutoSwitch(MainLoopContext* c) : _cntxt(c) { _cntxt -> switchIn(); }
	        ~AutoSwitch(){ _cntxt -> switchOut(); }
		private:
	        MainLoopContext* _cntxt;
	};
	friend class AutoSwitch;

	ConcurrentMainLoop* _ml;
	const Shell::Options& _opts;
	Problem* _prb;
private:
	Lib::Environment* _env;
	Lib::Environment* _temp_env; //A variable to preserve the current environment before switching in.
								 //TODO: a manager pattern for main loops needs to be implemented for context switching
	int _startTime, _endTime, _elapsed;
};

} /* namespace Kernel */

#endif /* __MainLoopContext__ */
