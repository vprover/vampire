#ifndef __SHELL__ANALYSIS__THEORY_SUBCLAUSE_ANALYSER__
#define __SHELL__ANALYSIS__THEORY_SUBCLAUSE_ANALYSER__

#include "Kernel/Clause.hpp"

using namespace Kernel;
namespace Shell {
  namespace Analysis {

      class TheorySubclauseAnalyser 
      {
        public: 
        TheorySubclauseAnalyser();
        ~TheorySubclauseAnalyser();
          /**
           * Adds a new clause for analysis. This shall be an ordenary clause. The theory subclause will be extracted in this function.
           */ 
          void addClause(Clause& c);
      };

  }
}

#endif // __SHELL__ANALYSIS__THEORY_SUBCLAUSE_ANALYSER__
