/**
 * @file compit2_impl.cpp
 * Defines implementation methods from compit2.hpp.
 */



#include "compit2.hpp"

#include "Lib/Allocator.hpp"
#include "Lib/Random.hpp"
#include "Lib/Set.hpp"
#include "Lib/Int.hpp"
#include "Lib/Timer.hpp"
#include "Lib/Exception.hpp"
#include "Lib/Environment.hpp"
#include "Lib/VirtualIterator.hpp"
#include "Lib/Metaiterators.hpp"

#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Curryfier.hpp"

#include "Indexing/TermSharing.hpp"
#include "Indexing/TermSubstitutionTree.hpp"

#include "Shell/Options.hpp"
#include "Shell/CommandLine.hpp"
#include "Shell/Property.hpp"
#include "Shell/Preprocess.hpp"
#include "Shell/Statistics.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Shell;
using namespace Indexing;

void compitInit(unsigned symCnt, unsigned fnSymCnt)
{
  Timer timer;
  timer.start();
  env.timer = &timer;
  env.signature = new Kernel::Signature;
  Indexing::TermSharing sharing;
  env.sharing = &sharing;

  Lib::Random::resetSeed();
  Allocator::setMemoryLimit(1000000000); //memory limit set to 1g

}

void compitAddSymbol(unsigned functor, unsigned arity)
{
  char buf[10];
  sprintf(buf,"f%d",functor);
  unsigned num=env.signature->addFunction(buf, arity);
  ASS_EQ(num,functor);
}


void compitTermBegin();
TermStruct compitTermVar(unsigned var);
TermStruct compitTermFn(unsigned functor);

void compitInsert(TermStruct t);
void compitDelete(TermStruct t);
unsigned compitQuery(TermStruct t);

