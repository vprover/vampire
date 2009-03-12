/**
 * @file Condensation.cpp
 * Implements class Condensation.
 */

#include "../Lib/VirtualIterator.hpp"
#include "../Lib/Metaiterators.hpp"
#include "../Lib/Int.hpp"
#include "../Lib/DArray.hpp"

#include "../Kernel/Term.hpp"
#include "../Kernel/Clause.hpp"
#include "../Kernel/MLMatcher.hpp"
#include "../Kernel/Ordering.hpp"
#include "../Kernel/Inference.hpp"
#include "../Kernel/Renaming.hpp"
#include "../Kernel/Matcher.hpp"
#include "../Kernel/RobSubstitution.hpp"

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

  static DArray<Literal*> newLits(32);
  static DArray<LiteralList*> alts(32);

  unsigned cLen=cl->length();
  unsigned newLen=cLen-1;
  CombinationIterator<unsigned> pairIt(0, cLen);
  while(pairIt.hasNext()) {
    pair<unsigned,unsigned> lpair=pairIt.next();
    Literal* l1=(*cl)[lpair.first];
    Literal* l2=(*cl)[lpair.second];

    newLits.ensure(newLen);

    RobSubstitution subst0;
    SubstIterator sit=subst0.unifiers(l1,0,l2,0,false);
    while(sit.hasNext()) {
      RobSubstitution* subst=sit.next();
      unsigned next=0;
      for(unsigned i=0;i<cLen;i++) {
        Literal* curr=(*cl)[i];
        if(curr!=l1) {
          newLits[next++] = subst->apply(curr,0);
        }
      }
      alts.init(newLen,0);
      bool success=false;

      for(unsigned bi=0;bi<newLen;bi++) {
	for(unsigned ii=0;ii<cLen;ii++) {
	  if(MatchingUtils::match(newLits[bi],(*cl)[ii],false)) {
	    LiteralList::push((*cl)[ii], alts[bi]);
	  }
	}
	if(!alts[bi]) {
	  goto match_fin;
	}
      }

      success=MLMatcher::canBeMatched(newLits.array(), newLen, cl,alts.array(),0,false);
    match_fin:
      for(unsigned i=0;i<newLen;i++) {
	alts[i]->destroy();
      }

      if(success) {
	Inference* inf = new Inference1(Inference::CONDENSATION, cl);
	Unit::InputType inpType = cl->inputType();
	Clause* res = new(newLen) Clause(newLen, inpType, inf);

	for(unsigned i=0;i<newLen;i++) {
	  (*res)[i] = newLits[i];
	}

	res->setAge(cl->age()+1);
	env.statistics->condensations++;
	keep=false;
	toAdd=pvi( getSingletonIterator(res) );
	return;
      }
    }
  }
  keep=true;
  toAdd=ClauseIterator::getEmpty();
}

}
