
/*
 * File compit2_impl.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file compit2_impl.cpp
 * Defines implementation methods from compit2.hpp.
 */



#include "compit2.hpp"

#include "Lib/Allocator.hpp"
#include "Lib/Random.hpp"
#include "Lib/Set.hpp"
#include "Lib/Stack.hpp"
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

Stack<TermList> assemblingStack(64);

void compitTermBegin()
{
  ASS(assemblingStack.isEmpty() || assemblingStack.length()==1);
  assemblingStack.reset();
}
TermStruct compitTermVar(unsigned var)
{
  assemblingStack.push(TermList(var,false));
  return assemblingStack.top();
}
TermStruct compitTermFn(unsigned functor)
{
  unsigned arity=env.signature->functionArity(functor);
  ASS_GE(assemblingStack.length(),arity);

  Term* trm=new(arity) Term();
  trm->makeSymbol(functor, arity);

  for(int i=arity-1;i>=0;i--) {
	*trm->nthArgument(i)=assemblingStack.pop();
  }

  assemblingStack.push(TermList(env.sharing->insert(trm)));
  return assemblingStack.top();
}


TermSubstitutionTree* getIndex()
{
  static TermSubstitutionTree* index=0;
  if(!index) {
    index=new TermSubstitutionTree();
  }
  return index;
}

void compitInsert(TermStruct t)
{
  getIndex()->insert(t,0,0);
}
void compitDelete(TermStruct t)
{
  getIndex()->remove(t,0,0);
}
unsigned compitQuery(TermStruct t)
{
  TermQueryResultIterator res=getIndex()->getUnifications(t,false);
  unsigned cnt=0;
  while(res.hasNext()) {
//    cout<<"fnd\t"<<res.next().term<<endl;
    res.next();
    cnt++;
  }
  return cnt;
}

