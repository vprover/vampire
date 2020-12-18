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
 * @file FastCondensation.cpp
 * Implements class FastCondensation.
 */

#include "Lib/DHMap.hpp"
#include "Lib/Int.hpp"
#include "Lib/TimeCounter.hpp"

#include "Kernel/Term.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Matcher.hpp"

#include "Lib/Environment.hpp"
#include "Shell/Statistics.hpp"

#include "FastCondensation.hpp"

#undef LOGGING
#define LOGGING 0

namespace Inferences {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

struct FastCondensation::CondensationBinder
{
  void init(DHMap<unsigned, int>* varMap_)
  {
    varMap=varMap_;
  }
  void reset()
  {
    bindings.reset();
  }
  bool bind(unsigned var, TermList term)
  {
    CALL("CondensationBinder::bind");

    if(varMap->get(var)==-1) {
      return term.isVar() && var==term.var();
    }

    TermList* binding;
    if(bindings.getValuePtr(var,binding,term)) {
      return true;
    }
    return *binding==term;
  }
  void specVar(unsigned var, TermList term)
  { ASSERTION_VIOLATION; }
private:
  DHMap<unsigned, int>* varMap;
  DHMap<unsigned, TermList> bindings;
};

Clause* FastCondensation::simplify(Clause* cl)
{
  CALL("FastCondensation::perform");

  TimeCounter tc(TC_CONDENSATION);

  unsigned clen=cl->length();
  if(clen<=1) {
    return cl;
  }

  //if variable is present in only one literal, the map contains its index,
  //otherwise it contains -1
  static DHMap<unsigned, int> varLits;
  varLits.reset();

  for(unsigned i=0;i<clen;i++) {
    VariableIterator vit((*cl)[i]);
    while(vit.hasNext()) {
      unsigned var=vit.next().var();
      int* pvlit;
      if(!varLits.getValuePtr(var, pvlit)) {
        if(*pvlit!=static_cast<int>(i)) {
          *pvlit=-1;
        }
      }
      else {
        *pvlit=i;
      }
    }
  }

  static CondensationBinder cbinder;
  cbinder.init(&varLits);

  for(unsigned cIndex=0;cIndex<clen;cIndex++) {
    Literal* cLit=(*cl)[cIndex];
    if(cLit->ground()) {
      //succeeding with ground literal would mean there are duplitace
      //literals in the clause, which should have already been removed
      continue;
    }
    for(unsigned mIndex=0;mIndex<clen;mIndex++) {
      if(mIndex==cIndex) {
        continue;
      }
      if(MatchingUtils::match(cLit, (*cl)[mIndex], false, cbinder)) {
        unsigned newLen=clen-1;
        Clause* res = new(newLen) Clause(newLen,
            SimplifyingInference1(InferenceRule::CONDENSATION, cl));

        unsigned ri=0;
        for(unsigned ci=0;ci<clen;ci++) {
          if(ci!=cIndex) {
            (*res)[ri++] = (*cl)[ci];
          }
        }
        ASS_EQ(ri, newLen);
 
        env.statistics->condensations++;
 
        return res;
      }
    }
  }
  return cl;
}

}
