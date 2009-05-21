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

#include "../Indexing/LiteralMiniIndex.hpp"

#include "../Saturation/SaturationAlgorithm.hpp"

#include "../Lib/Environment.hpp"
#include "../Shell/Statistics.hpp"

#include "Condensation.hpp"

namespace Inferences {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;


void Condensation::perform(Clause* cl, ForwardSimplificationPerformer* simplPerformer)
{
  CALL("Condensation::perform");

  static DArray<Literal*> newLits(32);
  static DArray<LiteralList*> alts(32);

  LiteralMiniIndex cmi(cl);

  unsigned cLen=cl->length();
  unsigned newLen=cLen-1;
  CombinationIterator<unsigned> pairIt(0, cLen);
  while(pairIt.hasNext()) {
    pair<unsigned,unsigned> lpair=pairIt.next();
    unsigned l1Index=lpair.first;
    unsigned l2Index=lpair.second;
    Literal* l1=(*cl)[l1Index];
    Literal* l2=(*cl)[l2Index];

    newLits.ensure(newLen);

    RobSubstitution subst0;
    SubstIterator sit=subst0.unifiers(l1,0,l2,0,false);
    while(sit.hasNext()) {
      RobSubstitution* subst=sit.next();
      alts.init(newLen,0);
      bool success=false;

      unsigned next=0;
      {
        Literal* lit=subst->apply(l1,0);
        newLits[next] = lit;
        LiteralMiniIndex::InstanceIterator iit(cmi, lit, false);
        if(!iit.hasNext()) {
          goto match_fin;
        }
        while(iit.hasNext()) {
	    LiteralList::push(iit.next(), alts[next]);
        }
        next++;
      }

      for(unsigned i=0;i<cLen;i++) {
        if(i!=l1Index && i!=l2Index) {
          Literal* lit=subst->apply((*cl)[i],0);
          newLits[next] = lit;
          LiteralMiniIndex::InstanceIterator iit(cmi, lit, false);
          if(!iit.hasNext()) {
            goto match_fin;
          }
          while(iit.hasNext()) {
	    LiteralList::push(iit.next(), alts[next]);
          }
          next++;
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

	res->setAge(cl->age());
	env.statistics->condensations++;

	simplPerformer->perform(0,res);
	ASS(!simplPerformer->clauseKept());
	return;
      }
    }
  }
}

}
