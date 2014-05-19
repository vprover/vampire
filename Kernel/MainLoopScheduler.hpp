/**
 * @file MainLoopScheduler.hpp
 *
 * @date 7 May 2014
 * @author dmitry
 */

#ifndef __MainLoopScheduler__
#define __MainLoopScheduler__

#include "MainLoop.hpp"
#include "ConcurrentMainLoop.hpp"
#include "MainLoopContext.hpp"

#include "Lib/List.hpp"

#include "Shell/Options.hpp"

#include "Lib/Environment.hpp"
//#include "Lib/Exception.hpp"

namespace Kernel {

using namespace Lib;

typedef List<Options*> OptionsList;
//typedef List<Problem*> ProblemList;
//typedef List<MainLoopContext*> MainLoopContextList;

class MainLoopScheduler {
public:
	MainLoopScheduler(Problem& prb, OptionsList& opts); //: _prb(prb), _opts(opts) {}
	//MainLoopScheduler(ProblemList& prbs, OptionsList& opts);
	virtual ~MainLoopScheduler();

    virtual MainLoopResult run();
	//static MainLoopScheduler* createFromOptions(Problem& prb, OptionsList* opts);

protected:


    //const Problem& _prb;
	//const OptionsList& _opts;
	//ConcurrentMainLoop** _mla;

private:

	MainLoopContext** _mlcl;
	unsigned int _mlclSize;

};

} /* namespace Kernel */

#endif /* __ConcurrentMainLoop__ */
