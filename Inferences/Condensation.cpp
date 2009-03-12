/**
 * @file Condensation.cpp
 * Implements class Condensation.
 */

#include "../Lib/VirtualIterator.hpp"
#include "../Lib/Metaiterators.hpp"
#include "../Lib/Int.hpp"

#include "../Kernel/Term.hpp"
#include "../Kernel/Clause.hpp"
#include "../Kernel/EqHelper.hpp"
#include "../Kernel/Ordering.hpp"
#include "../Kernel/Inference.hpp"
#include "../Kernel/Renaming.hpp"
#include "../Kernel/Matcher.hpp"

#include "../Indexing/Index.hpp"
#include "../Indexing/TermIndex.hpp"
#include "../Indexing/IndexManager.hpp"

#include "../Saturation/SaturationAlgorithm.hpp"

#include "../Lib/Environment.hpp"
#include "../Shell/Statistics.hpp"

#include "Condensation.hpp"

namespace Inferences {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;


void Condensation::perform(Clause* cl, bool& keep, ClauseIterator& toAdd)
{
  CALL("Condensation::perform");

  static Ordering* ordering=0;
  if(!ordering) {
    ordering=Ordering::instance();
  }

  unsigned cLen=cl->length();
  CombinationIterator<unsigned> pairIt(0, cLen);
  while(pairIt.hasNext()) {
    pair<unsigned,unsigned> lpair=pairIt.next();
    Literal* l1=(*cl)[lpair.first];
    Literal* l2=(*cl)[lpair.second];

    //TODO: finish
    NOT_IMPLEMENTED;

    Inference* inf = new Inference1(Inference::CONDENSATION, cl);
    Unit::InputType inpType = cl->inputType();

    Clause* res = new(cLen-1) Clause(cLen, inpType, inf);


    unsigned next=1;
    for(unsigned i=0;i<cLen;i++) {
      Literal* curr=(*cl)[i];
      if(curr!=l1) {
	(*res)[next++] = curr;
      }
    }

    res->setAge(cl->age()+1);
    env.statistics->condensations++;
    keep=false;
    toAdd=pvi( getSingletonIterator(res) );
    return;
  }
  keep=true;
  toAdd=ClauseIterator::getEmpty();
}

}
