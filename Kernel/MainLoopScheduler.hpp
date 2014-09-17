/**
 * @file MainLoopScheduler.hpp
 *
 * @since 7 May 2014
 * @author dmitry
 */

#ifndef __MainLoopScheduler__
#define __MainLoopScheduler__

#include <cstddef>
#include <iostream>

#include "Kernel/MainLoopFwd.hpp"
#include "Kernel/MainLoopContext.hpp"
#include "Kernel/ProblemFwd.hpp"
#include "Shell/OptionsListFwd.hpp"

//namespace Shell {

//class OptionsList;

//}

namespace Kernel {

//class MainLoopContext;
//class MainLoopResult;
//class Problem;

class MainLoopScheduler {
public:
	MainLoopScheduler(Problem& prb, Shell::OptionsList& opts);
	~MainLoopScheduler();

	MainLoopResult run();
	//static MainLoopScheduler* createFromOptions(Problem& prb, OptionsList* opts);

	static ConcurrentMainLoop* getCurrentMainLoop() {
		return MainLoopContext::currentContext -> getMainLoop();
	}

	static MainLoopContext* context() {
		return MainLoopContext::currentContext;
	}
// it won't compile in release mode if some of these are left in!
#if VDEBUG
	static std::ostream& log(){
		std::cout << MainLoopContext::currentContext->_id << ": ";
		return std::cout;
	}
#endif
protected:

private:
	// Store the context currently being run
    //static MainLoopContext* _currentContext;

	static MainLoopContext** _mlcl;
	static std::size_t _mlclSize;

};

} /* namespace Kernel */

#endif /* __ConcurrentMainLoop__ */
