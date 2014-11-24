/**
 * @file SaturationAlgorithmContext.hpp
 *
 * @since 23 May 2014
 * @author dmitry
 */

#ifndef __SaturationAlgorithmContext__
#define __SaturationAlgorithmContext__

//#include "Forwards.hpp"

#include <memory>

#include "Lib/DHMap.hpp"
//include "Lib/SmartPtr.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/MainLoopContext.hpp"

#include "Inferences/InferenceEngine.hpp"

//#include "SAT/SAT2FO.hpp"

//#include "Saturation/SSplitter.hpp"

//namespace Indexing {
//	class ClauseVariantIndex;
//}

namespace Indexing {
	class ClauseVariantIndex;
	class IndexManager;
}

namespace SAT {
	class SAT2FO;
}

namespace Saturation {

	class SSplitter;
	class SSplittingBranchSelector;

	class SaturationAlgorithmContext: public Kernel::MainLoopContext {
	public:
        CLASS_NAME(SaturationAlgorithmContext);
        USE_ALLOCATOR(SaturationAlgorithmContext);

		SaturationAlgorithmContext(Kernel::Problem& prb, Shell::Options& opts, bool join = false);

		~SaturationAlgorithmContext();

		const SSplitter* splitter() const { return _splitter; }
		Inferences::ImmediateSimplificationEngine* immediateSimplifier() const { return _immediateSimplifier.get(); };

		inline static Indexing::IndexManager& indexManager() { return _indexManager; }

	protected:
		// Switch into this context
		virtual void switchIn();
		// Switch out from the context
		virtual void switchOut();

	private:
		static bool _branchSelectorInitialised;
		static SSplittingBranchSelector _branchSelector;
		static Indexing::ClauseVariantIndex _componentIdx;
		static Lib::DHMap<Kernel::Clause*,Kernel::SplitLevel> _compNames;
		SSplitter* _splitter;
		//static ClauseVariantIndex _componentIdx;
		static SAT::SAT2FO _sat2fo;

		static std::unique_ptr<Inferences::ImmediateSimplificationEngine>_immediateSimplifier;

		static Indexing::IndexManager _indexManager;
	};

} /* namespace Saturation */

#endif /* __SaturationAlgorithmContext__ */
