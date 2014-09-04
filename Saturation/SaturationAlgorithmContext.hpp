/**
 * @file SaturationAlgorithmContext.hpp
 *
 * @since 23 May 2014
 * @author dmitry
 */

#ifndef __SaturationAlgorithmContext__
#define __SaturationAlgorithmContext__

#include "Kernel/MainLoopContext.hpp"

//#include "SAT/SAT2FO.hpp"

//#include "Saturation/SSplitter.hpp"

//namespace Indexing {
//	class ClauseVariantIndex;
//}

namespace Indexing {
	class ClauseVariantIndex;
}

namespace SAT {
	class SAT2FO;
}

namespace Saturation {

	class SSplitter;
	class SSplittingBranchSelector;

	class SaturationAlgorithmContext: public Kernel::MainLoopContext {
	public:
		SaturationAlgorithmContext(Kernel::Problem& prb, Shell::Options& opts);

		~SaturationAlgorithmContext();

		const SSplitter* splitter() const { return _splitter; }

	private:
		static bool _branchSelectorInitialised;
		static SSplittingBranchSelector _branchSelector;
		static Indexing::ClauseVariantIndex _componentIdx;
		SSplitter* _splitter;
		//static ClauseVariantIndex _componentIdx;
		static SAT::SAT2FO _sat2fo;
	};

} /* namespace Saturation */

#endif /* __SaturationAlgorithmContext__ */
