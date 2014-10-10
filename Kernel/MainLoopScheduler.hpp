/**
 * @file MainLoopScheduler.hpp
 *
 * @since 7 May 2014
 * @author dmitry
 */

#ifndef __MainLoopScheduler__
#define __MainLoopScheduler__

#include <cstddef>
#if VDEBUG
#include <iostream>
#endif//VDEBUG
#include <queue>

#include "Kernel/MainLoopFwd.hpp"
#include "Kernel/MainLoopContext.hpp"
#include "Kernel/ProblemFwd.hpp"
#include "Shell/OptionsList.hpp"

//namespace Shell {

//class OptionsList;

//}

namespace Kernel {

//class MainLoopContext;
//class MainLoopResult;
//class Problem;

class MainLoopScheduler {
public:
	MainLoopScheduler(Problem& prb, std::size_t capacity);
	MainLoopScheduler(Problem& prb, std::size_t capacity, Shell::OptionsList& opts);
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

	inline
	void addStrategy(const Shell::Options& opt){
		optionsQueue.push(opt);
	}

	void addStrategies(Shell::OptionsList& opts){
		Shell::OptionsList::Iterator i(opts);
	    while(i.hasNext()){
			addStrategy(i.next());
	    }
	}


protected:

private:

	Problem& _prb;
	MainLoopContext** _mlcl;
	std::size_t _capacity;

	class CompareOptions{
	public:
	    bool operator()(Shell::Options& lhs, Shell::Options& rhs) {
	       return ( &lhs < &rhs );
	    }
	};

	std::priority_queue<Shell::Options, std::vector<Shell::Options>, CompareOptions> optionsQueue;

	static MainLoopContext* createContext(Problem& prb, Shell::Options& opt);

};

} /* namespace Kernel */

#endif /* __ConcurrentMainLoop__ */
