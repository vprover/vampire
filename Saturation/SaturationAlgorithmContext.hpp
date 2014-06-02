/**
 * @file SaturationAlgorithmContext.hpp
 *
 * @date 23 May 2014
 * @author dmitry
 */

#ifndef __SaturationAlgorithmContext__
#define __SaturationAlgorithmContext__

#include "Saturation/SaturationAlgorithm.hpp"

#include "Kernel/Problem.hpp"
#include "Shell/Options.hpp"

namespace Saturation {

using Kernel::Problem;
using Shell::Options;

	class SaturationAlgorithmContext: public MainLoopContext {
	public:
		SaturationAlgorithmContext(Problem& prb, Options& opts);

		~SaturationAlgorithmContext();

		virtual void doStep();
		virtual void init();
		virtual void cleanup();
	};


} /* namespace Saturation */

#endif /* __SaturationAlgorithmContext__ */
