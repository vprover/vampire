/**
 * @file Grounding.cpp
 * Implements class Grounding.
 */

#include "../Lib/Stack.hpp"

#include "../Kernel/Clause.hpp"
#include "../Kernel/Signature.hpp"
#include "../Kernel/Term.hpp"

#include "Grounding.hpp"

namespace Shell
{

using namespace Lib;
using namespace Kernel;

struct Grounding::GroundingApplicator
{

};

ClauseList* Grounding::simplyGround(ClauseIterator clauses)
{
  Stack<TermList> constants;
  int funcs=env.signature->functions();
  for(int i=0;i<funcs;i++) {
    if(env.signature->functionArity(i)==0) {
      constants.push(TermList(Term::create(i,0,0)));
    }
  }

  ClauseList* res=0;

  NOT_IMPLEMENTED;

  return res;
}

}
