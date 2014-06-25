/**
 * @file SaturationAlgorithmContext.hpp
 *
 * @since 23 May 2014
 * @author dmitry
 */

#ifndef __SaturationAlgorithmContext__
#define __SaturationAlgorithmContext__

#include "Kernel/MainLoopContext.hpp"

namespace Saturation {

	class SaturationAlgorithmContext: public Kernel::MainLoopContext {
	public:
		SaturationAlgorithmContext(Kernel::Problem& prb, Shell::Options& opts);

		~SaturationAlgorithmContext();
	};

} /* namespace Saturation */

#endif /* __SaturationAlgorithmContext__ */
