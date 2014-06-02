/**
 * @file MainLoopContext.hpp
 *
 * @date 19 May 2014
 * @author dmitry
 */

#ifndef __MainLoopContext__
#define __MainLoopContext__

#include "Kernel/ConcurrentMainLoop.hpp"
#include "Kernel/Problem.hpp"
#include "Lib/Environment.hpp"
#include "Shell/Options.hpp"

namespace Kernel {

class MainLoopContext {
public:
	MainLoopContext(Problem& prb, Shell::Options& opt);

	virtual ~MainLoopContext();

	virtual void doStep() = 0;

	virtual void switchIn();

	virtual void switchOut();

	// Do init required by algorithm, and set phase
	virtual void init() = 0;
	// Do cleanup required by algorithm, and set phase
	virtual void cleanup() = 0;

protected:
	Problem& _prb;
	ConcurrentMainLoop* _ml;
	Environment* _env;
	Shell::Options& _opt;
private:
	Lib::Environment* _temp_env;

};

} /* namespace Kernel */

#endif /* __MainLoopContext__ */
