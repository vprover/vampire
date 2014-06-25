/**
 * @file IGAlgorithmContext.cpp
 *
 * @since 9 Jun 2014
 * @author dmitry
 */

#include "IGAlgorithmContext.hpp"

#include "Kernel/MainLoopContextFwd.hpp"
#include "Kernel/ProblemFwd.hpp"

#include "InstGen/IGAlgorithm.hpp"

namespace InstGen {

using Kernel::MainLoopContext;
using Kernel::Problem;
using Shell::Options;

IGAlgorithmContext::IGAlgorithmContext(Problem& prb, Options& opts):
		MainLoopContext(prb, opts) {
	CALL("IGAlgorithmContext::IGAlgorithmContext");

	switchIn();

	_ml = new IGAlgorithm(*_prb, opts);

	switchOut();
}

IGAlgorithmContext::~IGAlgorithmContext() {
	CALL("IGAlgorithmContext::~IGAlgorithmContext");
	switchIn();
	delete _ml;
	switchOut();
}

};
