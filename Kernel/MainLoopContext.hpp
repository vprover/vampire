/**
 * @file MainLoopContext.hpp
 *
 * @since 19 May 2014
 * @author dmitry
 */

#ifndef __MainLoopContext__
#define __MainLoopContext__

#include <iostream>

#include "Lib/EnvironmentFwd.hpp"
#include "Kernel/ConcurrentMainLoopFwd.hpp"
#include "Kernel/ProblemFwd.hpp"
#include "Shell/OptionsFwd.hpp"

namespace Kernel {


class MainLoopContext {
public:
	MainLoopContext(Problem& prb, Shell::Options& opts, bool join = false);
#if VDEBUG
	const unsigned _id;
#endif

	virtual ~MainLoopContext();

	// Do one main loop step in this context
	virtual void doStep(unsigned int timeSlice = 100);
	// Do init required by algorithm, and set phase
	virtual void init();
	// Do cleanup required by algorithm, and set phase
	virtual void cleanup();

	// Get the ConcurrentMainLoop
	ConcurrentMainLoop* getMainLoop() const { return _ml; }

	unsigned int updateTimeCounter();
	unsigned int elapsedDeciseconds() const {
		return _elapsed / 100;
	}
	unsigned int elapsed() const {
		return _elapsed;
	}

#if VDEBUG
	bool checkEnvironment(const Lib::Environment* env) const {
		return (_env == env);
	}
#endif //VDEBUG

	static MainLoopContext* currentContext;

	inline
	bool initialised() const { return _initialised; }

	inline
	unsigned int averageTimeSlice() const {
		return (_elapsed / _steps);
	}

protected:
	// Switch into this context
	virtual void switchIn();
	// Switch out from the context
	virtual void switchOut();

	class AutoSwitch{
		public:
	        AutoSwitch(MainLoopContext* c) : _cntxt(c) { _cntxt -> switchIn(); }
	        ~AutoSwitch(){ _cntxt -> switchOut(); }
		private:
	        MainLoopContext* _cntxt;
	};
	friend class AutoSwitch;

	template<class T>
	class TypedAutoSwitch{
			public:
		        TypedAutoSwitch(T* c) : _cntxt(c) { _cntxt -> T::switchIn(); }
		        ~TypedAutoSwitch(){ _cntxt -> T::switchOut(); }
			private:
		        T* _cntxt;
	};
	template<class T>
	friend class TypedAutoSwitch;


	ConcurrentMainLoop* _ml;
	const Shell::Options& _opts;
	Problem* _prb;
private:
#if VDEBUG
        static unsigned id_counter;
#endif
	Lib::Environment* _env;
	Lib::Environment* _temp_env; //A variable to preserve the current environment before switching in.
								 //TODO: a manager pattern for main loops needs to be implemented for context switching
	unsigned int _startTime, _elapsed;

	bool _initialised;

	unsigned int _steps;
};

} /* namespace Kernel */

#endif /* __MainLoopContext__ */
