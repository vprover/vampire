/**
 * @file IGAlgorithmContext.hpp
 *
 * @since 9 June 2014
 * @author dmitry
 */

#ifndef __IGAlgorithmContext__
#define __IGAlgorithmContext__

#include "Kernel/MainLoopContext.hpp"

namespace InstGen {

	class IGAlgorithmContext: public Kernel::MainLoopContext {
	public:
		IGAlgorithmContext(Kernel::Problem& prb, Shell::Options& opts);

		~IGAlgorithmContext();
	};

} /* namespace InstGen */

#endif /* __IGAlgorithmContext__ */
