/**
 * @file MainLoopScheduler.hpp
 *
 * @since 7 May 2014
 * @author dmitry
 */

#ifndef __MainLoopScheduler__
#define __MainLoopScheduler__

#include "Shell/Options.hpp"

namespace Kernel {

class MainLoopContext;
class MainLoopResult;
class Problem;

class MainLoopScheduler {
public:
	MainLoopScheduler(Problem& prb, Shell::OptionsList& opts);
	//MainLoopScheduler(ProblemList& prbs, OptionsList& opts);
	virtual ~MainLoopScheduler();

    virtual MainLoopResult run();
	//static MainLoopScheduler* createFromOptions(Problem& prb, OptionsList* opts);

protected:

private:

	MainLoopContext** _mlcl;
	unsigned int _mlclSize;

};

} /* namespace Kernel */

#endif /* __ConcurrentMainLoop__ */
