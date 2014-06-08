/**
 * @file MainLoopContext.hpp
 *
 * @since 19 May 2014
 * @author dmitry
 */

#ifndef __MainLoopContext__
#define __MainLoopContext__

namespace Lib {

class Environment;

}

namespace Shell {

class Options;

}

namespace Kernel {

class Problem;
class ConcurrentMainLoop;

class MainLoopContext {
public:
	MainLoopContext(Problem& prb, const Shell::Options& opt);

	virtual ~MainLoopContext();

	// Do one main loop step in this context
	virtual void doStep() = 0;

	// Switch into this context
	virtual void switchIn();

	// Switch out from the context
	virtual void switchOut();

	// Do init required by algorithm, and set phase
	virtual void init() = 0;
	// Do cleanup required by algorithm, and set phase
	virtual void cleanup() = 0;

protected:
	Problem& _prb;
	ConcurrentMainLoop* _ml;
	Lib::Environment* _env;
	const Shell::Options& _opt;
private:
	Lib::Environment* _temp_env; //A variable to preserve the current environment before switching in.
								 //TODO: a manager pattern for main loops needs to be implemented for context switching
};

} /* namespace Kernel */

#endif /* __MainLoopContext__ */
