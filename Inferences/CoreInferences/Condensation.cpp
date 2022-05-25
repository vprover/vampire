/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file Condensation.cpp
 * Implements class Condensation.
 */

#include "Lib/DArray.hpp"
#include "Lib/Int.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/TimeCounter.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/Term.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/MLMatcher.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Renaming.hpp"
#include "Kernel/Matcher.hpp"
#include "Kernel/RobSubstitution.hpp"

#include "Indexing/LiteralMiniIndex.hpp"

#include "Lib/Environment.hpp"
#include "Shell/Statistics.hpp"

#include "Condensation.hpp"

namespace Inferences {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

Clause* Condensation::simplify(Clause* cl)
{
  CALL("Condensation::perform");
  TimeCounter tc(TC_CONDENSATION);

  unsigned clen=cl->length();
  if(clen<=1) {
    return cl;
  }
  unsigned newLen=clen-1;

  // stores newLen new literals
  static DArray<Literal*> newLits(32);
  //
  static DArray<LiteralList*> alts(32);
  //static OCMatchIterator matcher;

  LiteralMiniIndex cmi(cl);

  // For each pair of non-equal literals l1 and l2
  //
  CombinationIterator<unsigned> pairIt(0, clen);
  while(pairIt.hasNext()) {
    pair<unsigned,unsigned> lpair=pairIt.next();
    unsigned l1Index=lpair.first;
    unsigned l2Index=lpair.second;
    if(l1Index==l2Index) {
      continue;
    }
    Literal* l1=(*cl)[l1Index];
    Literal* l2=(*cl)[l2Index];

    newLits.ensure(newLen);

    RobSubstitution subst0;
    // For each unifying subst of l1 and l2
    // apply the subst to l1 and search for instances of this in the clause
    // (note that this is symmetric to applying subst to l2)
    SubstIterator sit=subst0.unifiers(l1,0,l2,0,false);
    while(sit.hasNext()) {
      RobSubstitution* subst=sit.next();
      alts.init(newLen,0);
      bool success=false;

      unsigned next=0;
      {
        Literal* lit=subst->apply(l1,0);
        newLits[next] = lit;
        // Use lit as a query to find instances of it in cmi (i.e. the clause)
        LiteralMiniIndex::InstanceIterator iit(cmi, lit, false);
        if(!iit.hasNext()) {
          // If there are no instances then finish
          goto match_fin;
        }
        // Store all instances in alts (alts[next] is a literal list)
        while(iit.hasNext()) {
	    LiteralList::push(iit.next(), alts[next]);
        }
        next++;
      }

      // For all literals that are not l1 or l2
      // apply the subst and search for instances of the result as before
      for(unsigned i=0;i<clen;i++) {
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

      // I think this is asking if there is a substitution that will match
      // each lit in newLits with one of its instances in alts
      // CHECK!
      success=MLMatcher::canBeMatched(newLits.array(), newLen, cl,alts.array(),0,false);

    // We will jump here if we do not find a match, in this case success will be false
    match_fin:
      for(unsigned i=0;i<newLen;i++) {
        LiteralList::destroy(alts[i]);
      }

      if(success) {
        Clause* res = new(newLen) Clause(newLen, SimplifyingInference1(InferenceRule::CONDENSATION, cl));
        Renaming norm;

        for(unsigned i=0;i<newLen;i++) {
          //(*res)[i] = norm.normalize(newLits[i]);
          (*res)[i] = newLits[i];
        }

        env.statistics->condensations++;
        return res;
      }
    }
  }
  return cl;
}

}
