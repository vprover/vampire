
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"


#include "ApplicativeHelper.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Shell;

TermList ApplicativeHelper::createAppTerm(TermList sort, TermList arg1, TermList arg2, TermList arg3, TermList arg4)
{
  CALL("ApplicativeHelper::createAppTerm/3");

  TermList t1 = createAppTerm3(sort, arg1, arg2, arg3);
  return createAppTerm(SortHelper::getResultSort(t1.term()), t1, arg4);
}

TermList ApplicativeHelper::createAppTerm3(TermList sort, TermList arg1, TermList arg2, TermList arg3)
{
  CALL("ApplicativeHelper::createAppTerm3");
  
  TermList s1 = getNthArg(sort, 1);
  TermList s2 = getResultApplieadToNArgs(sort, 1);
  TermList s3 = getNthArg(s2, 1);
  TermList s4 = getResultApplieadToNArgs(s2, 1);
  return createAppTerm(s3, s4, createAppTerm(s1, s2, arg1, arg2), arg3);
}

TermList ApplicativeHelper::createAppTerm(TermList sort, TermList arg1, TermList arg2)
{
  CALL("ApplicativeHelper::createAppTerm/2");
  
  TermList s1 = getNthArg(sort, 1);
  TermList s2 = getResultApplieadToNArgs(sort, 1);
  return createAppTerm(s1, s2, arg1, arg2);
}

TermList ApplicativeHelper::createAppTerm(TermList s1, TermList s2, TermList arg1, TermList arg2)
{
  CALL("ApplicativeHelper::createAppTerm/1");
 
  static TermStack args;
  args.reset();
  args.push(s1);
  args.push(s2);
  args.push(arg1);
  args.push(arg2);
  unsigned app = env.signature->getApp();
  return TermList(Term::create(app, 4, args.begin()));
}

TermList ApplicativeHelper::createAppTerm(TermList sort, TermList head, TermStack& terms)
{
  CALL("ApplicativeHelper::createAppTerm/4");
  ASS(head.isVar() || SortHelper::getResultSort(head.term()) == sort);

  TermList res = head;
  TermList s1, s2;

  for(int i = terms.size() - 1; i >= 0; i--){
    s1 = getNthArg(sort, 1);
    s2 = getResultApplieadToNArgs(sort, 1);
    res = createAppTerm(s1, s2, res, terms[i]);
    sort = s2;
  }
  return res; 

}

/** indexed from 1 */
TermList ApplicativeHelper::getResultApplieadToNArgs(TermList arrowSort, unsigned argNum)
{
  CALL("ApplicativeHelper::getResultApplieadToNArgs");
  
  while(argNum > 0){
    ASS(arrowSort.isTerm() && env.signature->getFunction(arrowSort.term()->functor())->arrow());
    arrowSort = *arrowSort.term()->nthArgument(1);
    argNum--;
  }
  return arrowSort;
}


/** indexed from 1 */
TermList ApplicativeHelper::getNthArg(TermList arrowSort, unsigned argNum)
{
  CALL("ApplicativeHelper::getNthArg");
  ASS(argNum > 0);

  TermList res;
  while(argNum >=1){
    ASS(arrowSort.isTerm() && env.signature->getFunction(arrowSort.term()->functor())->arrow());
    res = *arrowSort.term()->nthArgument(0);
    arrowSort = *arrowSort.term()->nthArgument(1);
    argNum--;
  }
  return res;
}

TermList ApplicativeHelper::getResultSort(TermList sort)
{
  CALL("ApplicativeHelper::getResultSort");

  while(sort.isTerm() && env.signature->getFunction(sort.term()->functor())->arrow()){
    sort = *sort.term()->nthArgument(1);
  }
  return sort;
}

void ApplicativeHelper::getHeadAndArgs(TermList term, TermList& head, TermStack& args)
{
  CALL("ApplicativeHelper::getHeadAndArgs");

  if(!term.isTerm()){
  	head = term;
  	return;
  }

  while(env.signature->getFunction(term.term()->functor())->app()){
    args.push(*term.term()->nthArgument(3)); 
    term = *term.term()->nthArgument(2);
    if(!term.isTerm()){ break; } 
  }
  head = term;

}
