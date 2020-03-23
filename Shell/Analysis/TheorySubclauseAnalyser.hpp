#ifndef __SHELL__ANALYSIS__THEORY_SUBCLAUSE_ANALYSER__
#define __SHELL__ANALYSIS__THEORY_SUBCLAUSE_ANALYSER__

#include <iostream>
#include "Kernel/Clause.hpp"
#include "Shell/Analysis/TheorySubclauseAnalyser/AbstractLiteralContainer.hpp"
#include "Lib/vstd.h"
#include "Lib/macro_magic.h"

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

#define EQ_CLASSES 1, 2

#define DECLARE_EQ_CLASS(i) \
  struct LitEquiv ## i;\
  template<> struct EquivalenceClass<LitEquiv ## i> { \
    using less = struct { \
      bool operator()(const rc<AbsLiteral>& lhs, const rc<AbsLiteral>& rhs) const; \
    }; \
  }; \

MAP(DECLARE_EQ_CLASS, EQ_CLASSES)
#undef DECLARE_EQ_CLASS

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


#define DECLARE_EQ_CLAS_MEMBERS(i) \
    using equiv_t_ ## i  = Container<rc<AbsLiteral>, LitEquiv ## i>; \
    equiv_t_ ## i  _eq ## i; \


            MAP(DECLARE_EQ_CLAS_MEMBERS, EQ_CLASSES)

#undef DECLARE_EQ_CLAS_MEMBERS

        public:
          static TheorySubclauseAnalyser* instance;
        };

    }
}

#endif // __SHELL__ANALYSIS__THEORY_SUBCLAUSE_ANALYSER__;
