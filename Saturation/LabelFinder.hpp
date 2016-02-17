/**
 * @file LabelFinder.hpp
 * Defines class LabelFinder
 *
 * @author Giles
 * @since 3/02/2016
 */

#ifndef __LabelFinder__
#define __LabelFinder__

#include "Forwards.hpp"

#include "Lib/Allocator.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/Clause.hpp"

namespace Saturation {

using namespace Kernel;
using namespace Inferences;

class LabelFinder {
public:
  CLASS_NAME(LabelFinder);
  USE_ALLOCATOR(LabelFinder);
  
  ~LabelFinder();

  void onNewPropositionalClause(Clause* cl);

  Stack<unsigned> getFoundLabels(){ return _foundLabels;}

  Clause* getLabelClause(unsigned label){
    Clause* c;
    if(_clauses.find(label,c)) return c;
    return 0;
  }

private:

  Stack<unsigned> _foundLabels;
  DHMap<unsigned,Clause*> _clauses;

};

}

#endif // __LabelFinder__
