#ifndef __SHELL__ANALYSIS__THEORY_SUBCLAUSE_ANALYSER__
#define __SHELL__ANALYSIS__THEORY_SUBCLAUSE_ANALYSER__

#include <iostream>
#include "Kernel/Clause.hpp"
#include "Shell/Analysis/TheorySubclauseAnalyser/AbstractLiteralContainer.hpp"
#include "Lib/vstd.h"

#ifdef VDEBUG
#define IF_DEBUG(...) __VA_ARGS__
#else
#define IF_DEBUG(...)
#endif

/* template stuff */
#include <memory>
#include <vector>
#include <set>
#include <map>
#include <unordered_map>
#include <unordered_set>
#include <functional>

/* ================================================= */
/* =================== collections ================= */
/* ================================================= */

class AbsLiteral;

class AbsTerm;


struct LitEquiv1;
template<>
struct EquivalenceClass<LitEquiv1> {
  using less = struct {
    bool operator()(const rc<AbsLiteral>& lhs, const rc<AbsLiteral>& rhs) const;
  };
};

using namespace Kernel;
namespace Shell {
    namespace Analysis {

        class TheorySubclauseAnalyser {
          CLASS_NAME(TheorySubclauseAnalyser)
          USE_ALLOCATOR(TheorySubclauseAnalyser)
        public:
            TheorySubclauseAnalyser();

            ~TheorySubclauseAnalyser();

            /**
             * Adds a new clause for analysis.
             *
             * This shall be an ordenary clause. The theory subclause will be extracted within this function.
             */
            void addClause(Clause &c);

            /**
             * Dumps the result of the analysis to @b ostream.
             */
            void dumpStats(std::ostream &out) const;

        private:
            using literals_type = Container<rc<AbsLiteral>, Equality<rc<AbsLiteral> > >;
            literals_type _literals;


            using equiv1_t = Container<rc<AbsLiteral>, LitEquiv1>;
            equiv1_t _eq1;
        public:
          static TheorySubclauseAnalyser* instance;
        };

    }
}

#endif // __SHELL__ANALYSIS__THEORY_SUBCLAUSE_ANALYSER__;
