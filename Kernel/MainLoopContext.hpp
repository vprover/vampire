/**
 * @file MainLoopContext.hpp
 *
 * @date 19 May 2014
 * @author dmitry
 */

#ifndef __MainLoopContext__
#define __MainLoopContext__

#include "Kernel/Problem.hpp"

#include "Shell/Options.hpp"
#include "Lib/Environment.hpp"

namespace Kernel {

using Lib::Environment;
using Shell::Options;

class MainLoopContext {
public:
	MainLoopContext(Problem& prb, Options& opt);

	virtual ~MainLoopContext();

	virtual void doStep() = 0;

	virtual void switchIn();

	virtual void switchOut();

protected:
	Problem& _prb;
	ConcurrentMainLoop* _ml;
	Environment* _env;
	Options& _opt;
private:
	Environment* _temp_env;

};

} /* namespace Kernel */

#endif /* __MainLoopContext__ */
