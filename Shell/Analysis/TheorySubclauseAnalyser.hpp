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

// using my_hash = EquivalenceClass<Equality<rc<AbsLiteral>>>::hash;
// using my_equal = EquivalenceClass<Equality<rc<AbsLiteral>>>::equal;
// static_assert(__check_hash_requirements<rc<AbsLiteral>,my_hash>::value, "__check_hash_requirements");
// static_assert(is_copy_constructible<my_hash>::value, "is_copy_constructible");
// static_assert(is_move_constructible<my_hash>::value, "is_move_constructible");
// static_assert(__invokable_r<size_t, my_hash, rc<AbsLiteral> const &>::value, "__invokable_r");

using namespace Kernel;
namespace Shell {
    namespace Analysis {

        class TheorySubclauseAnalyser {
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
//            unordered_multiset<rc<AbsLiteral>, my_hash, my_equal> my_set;
//            Container<rc<AbsLiteral>, Equality<rc<AbsLiteral> > > cont;
//            using literals_type = EquivalenceClass<Equality<rc<AbsLiteral>>>;
            using literals_type = Container<rc<AbsLiteral>, Equality<rc<AbsLiteral> > >;
            literals_type _literals;
        };

    }
}

#endif // __SHELL__ANALYSIS__THEORY_SUBCLAUSE_ANALYSER__;
