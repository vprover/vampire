/**
 * @file SaturationAlgorithmContext.cpp
 *
 * @since 2 Jun 2014
 * @author dmitry
 */

#include "SaturationAlgorithmContext.hpp"

#include "Kernel/MainLoopContextFwd.hpp"
#include "Kernel/ProblemFwd.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

namespace Saturation {

using Kernel::MainLoopContext;
using Kernel::Problem;
using Shell::Options;

SaturationAlgorithmContext::SaturationAlgorithmContext(Problem& prb, Options& opts):
		MainLoopContext(prb, opts) {
	CALL("SaturationAlgorithmContext::SaturationAlgorithmContext");

	AutoSwitch(this);
	_ml = SaturationAlgorithm::createFromOptions(*_prb, opts);
}

SaturationAlgorithmContext::~SaturationAlgorithmContext() {
	CALL("SaturationAlgorithmContext::~SaturationAlgorithmContext");

	delete _ml;
}

};
