/**
 * @file SaturationAlgorithmContext.cpp
 *
 * @date 2 Jun 2014
 * @author dmitry
 */

#include "Saturation/SaturationAlgorithm.hpp"

#include "Kernel/MainLoopContext.hpp"
#include "Kernel/Problem.hpp"
#include "Shell/Options.hpp"
#include "Lib/Timer.hpp"

#include "SaturationAlgorithmContext.hpp"

namespace Saturation {

using Kernel::MainLoopContext;
using Kernel::Problem;
using Shell::Options;
using Lib::Timer;

SaturationAlgorithmContext::SaturationAlgorithmContext(Problem& prb, Options& opts): MainLoopContext(prb, opts) {
			CALL("SaturationAlgorithmContext::SaturationAlgorithmContext(Problem& prb, Options& opts)");

			switchIn();

			_ml = SaturationAlgorithm::createFromOptions(_prb, _opt);

			switchOut();
		}

SaturationAlgorithmContext::~SaturationAlgorithmContext() {
			CALL("SaturationAlgorithmContext::~SaturationAlgorithmContext()");

			delete _ml;
		}

void SaturationAlgorithmContext::init(){
	CALL("SaturationAlgorithmContext::init");

	switchIn();

	_env -> statistics -> phase = Statistics::SATURATION;
	_ml -> initAlgorithmRun();

	switchOut();
}

void SaturationAlgorithmContext::cleanup(){
	CALL("SaturationAlgorithmContext::cleanup");

	switchIn();

	_env -> statistics -> phase = Statistics::FINALIZATION;
	_ml -> updateStatistics();

	switchOut();
}

void SaturationAlgorithmContext::doStep() {
			CALL("SaturationAlgorithmContext::doStep()");

			switchIn();
			_ml -> doOneAlgorithmStep();

			Timer::syncClock();
			if (env -> timeLimitReached()) {
				throw  TimeLimitExceededException();
			}

			switchOut();
		}

	};
