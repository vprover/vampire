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
	MainLoopContext(Problem& prb, const Shell::Options& opts);

	virtual ~MainLoopContext();

	// Do one main loop step in this context
	virtual void doStep();
	// Do init required by algorithm, and set phase
	virtual void init();
	// Do cleanup required by algorithm, and set phase
	virtual void cleanup();

protected:
	// Switch into this context
	void switchIn();
	// Switch out from the context
	void switchOut();

	ConcurrentMainLoop* _ml;
private:
	Problem& _prb;
	Lib::Environment* _env;
	const Shell::Options& _opts;
	Lib::Environment* _temp_env; //A variable to preserve the current environment before switching in.
								 //TODO: a manager pattern for main loops needs to be implemented for context switching
};

} /* namespace Kernel */

#endif /* __MainLoopContext__ */
