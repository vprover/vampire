/**
 * @file ConcurrentMainLoop.hpp
 *
 * @date 7 May 2014
 * @author dmitry
 */

#ifndef __ConcurrentMainLoop__
#define __ConcurrentMainLoop__


namespace Kernel {

class ConcurrentMainLoop {
public:
	ConcurrentMainLoop() {}
	virtual ~ConcurrentMainLoop() {}

	virtual void initAlgorithmRun() = 0;
	virtual void doOneAlgorithmStep() = 0;
};

} /* namespace Kernel */

#endif /* __ConcurrentMainLoop__ */
