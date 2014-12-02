/**
 * @file SaturationAlgorithmContext.cpp
 *
 * @since 2 Jun 2014
 * @author dmitry
 */

#include "SaturationAlgorithmContext.hpp"

#include "Kernel/MainLoopContextFwd.hpp"
#include "Kernel/ProblemFwd.hpp"

//#include "Lib/SmartPtr.hpp"

#include "Indexing/IndexManager.hpp"

#include "SAT/SAT2FO.hpp"

#include "Saturation/SaturationAlgorithm.hpp"
#include "Saturation/SSplitter.hpp"

namespace Saturation {

using Kernel::MainLoopContext;
using Kernel::Problem;
using Shell::Options;
using SAT::SAT2FO;

bool SaturationAlgorithmContext::_branchSelectorInitialised = false;
SAT2FO SaturationAlgorithmContext::_sat2fo;
SSplittingBranchSelector SaturationAlgorithmContext::_branchSelector(&SaturationAlgorithmContext::_sat2fo);
ClauseVariantIndex SaturationAlgorithmContext::_componentIdx;
Lib::DHMap<Kernel::Clause*,Kernel::SplitLevel> SaturationAlgorithmContext::_compNames;

std::unique_ptr<Inferences::ImmediateSimplificationEngine> SaturationAlgorithmContext::_immediateSimplifier;
Indexing::IndexManager SaturationAlgorithmContext::_indexManager;

SaturationAlgorithmContext::SaturationAlgorithmContext(Problem& prb, Options& opts, bool join):
		MainLoopContext(prb, opts, join) {
	CALL("SaturationAlgorithmContext::SaturationAlgorithmContext");

#if VDEBUG
	std::cout << "Creating context for saturation algorithm " << _id << std::endl;
#endif //VDEBUG

	TypedAutoSwitch<MainLoopContext> s(this);
	//[dmitry] immediate simplifier must be initialised before creation of saturation algorithms
	if( ! (_immediateSimplifier) ){
#if VDEBUG
	std::cout << "Initialising immediate simplifier for saturation algorithms" << std::endl;
#endif //VDEBUG
		_immediateSimplifier.reset(SaturationAlgorithm:: createISE(*_prb, opts));
	}

	SaturationAlgorithm* sa = SaturationAlgorithm::create(*_prb, opts);
	_ml = sa;
    sa -> initFromOptions(*_prb, opts);
    //_indexManager.request(Indexing::GENERATING_SUBST_TREE);

	if(opts.splitting()){

		_splitter = sa -> splitter();//[dmitry] TODO: Merge Splitter and SSplitter

		if(!_branchSelectorInitialised){
			_branchSelector.init(opts);
			_branchSelectorInitialised = true;
		}

		_splitter -> setBranchSelector(&_branchSelector);
		_splitter -> setComponentIndex(&_componentIdx);
		_splitter -> setSAT2FO(&_sat2fo);
		_splitter -> setComponentNames(&_compNames);
	}
	//_indexManager.setSaturationAlgorithm(sa);
}

SaturationAlgorithmContext::~SaturationAlgorithmContext() {
	CALL("SaturationAlgorithmContext::~SaturationAlgorithmContext");

#if VDEBUG
	std::cout << "Deleting context for saturation algorithm " << _id << std::endl;
#endif //VDEBUG

	TypedAutoSwitch<MainLoopContext> s(this);
//	_indexManager.release(Indexing::GENERATING_SUBST_TREE);
	delete _ml;
}

void SaturationAlgorithmContext::switchIn(){
	CALL("SaturationAlgorithmContext::switchIn");

	MainLoopContext::switchIn();
	ASS(_ml);
	ASS(_immediateSimplifier);

#if VDEBUG
	std::cout << "Attaching saturation algorithm to immediate simplifier" << std::endl;
#endif //VDEBUG
	 SaturationAlgorithm* sa = static_cast<SaturationAlgorithm*>(_ml);
	_immediateSimplifier ->attach(sa);
	//_indexManager -> attach(sa);
}

void SaturationAlgorithmContext::switchOut(){
	CALL("SaturationAlgorithmContext::switchOut");

	ASS(_immediateSimplifier && _immediateSimplifier ->attached());
#if VDEBUG
	std::cout << "Detaching saturation algorithm from immediate simplifier" << std::endl;
#endif //VDEBUG
	//_indexManager -> detach();
	_immediateSimplifier -> detach();
	MainLoopContext::switchOut();
}

};
