/**
 * @file MainLoopScheduler.hpp
 *
 * @date 7 May 2014
 * @author dmitry
 */

#ifndef __MainLoopScheduler__
#define __MainLoopScheduler__

#include "Kernel/MainLoop.hpp"
#include "Kernel/MainLoopContext.hpp"
#include "Lib/List.hpp"
#include "Shell/Options.hpp"

namespace Kernel {

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
