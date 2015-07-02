/**
 * @file SortInference.cpp
 * Implements class SortInference.
 */

#include "Kernel/Term.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"

#include "Lib/Array.hpp"
#include "Lib/Environment.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/IntUnionFind.hpp"

#include "SortInference.hpp"

#define DEBUG_SORT_INFERENCE 0


namespace FMB 
{


/**
 * We assume this occurs *after* flattening so all literals are shallow
 *
 */
SortedSignature* SortInference::apply(ClauseIterator cit)
{
  CALL("SortInference::run");

  Array<unsigned> offset_f(env.signature->functions());
  Array<unsigned> offset_p(env.signature->predicates());

  unsigned count = 0;
  for(unsigned f=0; f < env.signature->functions();f++){
    offset_f[f] = count;
    count += (1+env.signature->getFunction(f)->arity());
  }

#if DEBUG_SORT_INFERENCE
  cout << "just functions count is " << count << endl;
#endif

  // skip 0 because it is always equality
  for(unsigned p=1; p < env.signature->predicates();p++){
    offset_p[p] = count;
    count += (env.signature->getPredicate(p)->arity());
  }

#if DEBUG_SORT_INFERENCE
  cout << "count is " << count << endl;
#endif

  IntUnionFind unionFind(count);

  while(cit.hasNext()){
   Clause* c = cit.next();
  
   //cout << "CLAUSE " << c->toString() << endl;

   Array<Stack<unsigned>> varPositions(c->varCnt());
   IntUnionFind localUF(c->varCnt());
   for(unsigned i=0;i<c->length();i++){
     Literal* l = (*c)[i];
     if(l->isEquality()){
       if(l->isTwoVarEquality()){
#if DEBUG_SORT_INFERENCE
         cout << "join X" << l->nthArgument(0)->var()<< " and X" << l->nthArgument(1)->var() << endl;
#endif
         localUF.doUnion(l->nthArgument(0)->var(),l->nthArgument(1)->var());
       }else{
         ASS(!l->nthArgument(0)->isVar());
         ASS(l->nthArgument(1)->isVar());
         Term* t = l->nthArgument(0)->term();
         unsigned f = t->functor();
         unsigned n = offset_f[f];
         varPositions[l->nthArgument(1)->var()].push(n);
#if DEBUG_SORT_INFERENCE
         cout << "push " << n << " for X" << l->nthArgument(1)->var() << endl;
#endif
         for(unsigned i=0;i<t->arity();i++){
           ASS(t->nthArgument(i)->isVar());
           varPositions[t->nthArgument(i)->var()].push(n+1+i);
#if DEBUG_SORT_INFERENCE
           cout << "push " << (n+1+i) << " for X" << t->nthArgument(i)->var() << endl;
#endif
         }
       }
     }
     else{
       unsigned n = offset_p[l->functor()];
       for(unsigned i=0;i<l->arity();i++){
           ASS(l->nthArgument(i)->isVar());
           varPositions[l->nthArgument(i)->var()].push(n+i);
#if DEBUG_SORT_INFERENCE
           cout << "push " << (n+i) << " for X" << l->nthArgument(i)->var() << endl;
#endif
       }
     }
   } 
   for(unsigned v=0;v<varPositions.size();v++){
     unsigned x = localUF.root(v);
     if(x!=v){
       varPositions[x].loadFromIterator(Stack<unsigned>::Iterator(varPositions[v])); 
       varPositions[v].reset();
     }
   }
   for(unsigned v=0;v<varPositions.size();v++){
     Stack<unsigned> stack = varPositions[v];
     if(stack.size()<=1) continue;
     // for each pair of stuff in the stack say that they are the same
     for(unsigned i=0;i<stack.size();i++){
       for(unsigned j=i+1;j<stack.size();j++){
#if DEBUG_SORT_INFERENCE
         cout << "doing union " << stack[i] << " and " << stack[j] << endl;
#endif
         unionFind.doUnion(stack[i],stack[j]);
       }
     }
   }

  }
  unionFind.evalComponents();
  unsigned comps = unionFind.getComponentCount();

#if DEBUG_SORT_INFERENCE
  cout << comps << " components" << endl;
#endif

  SortedSignature* sig = new SortedSignature();
  sig->sorts=comps;
  sig->sortedConstants.ensure(comps);
  sig->sortedFunctions.ensure(comps);

  DHMap<int,unsigned> translate;
  unsigned seen = 0;

  for(unsigned f=0;f<env.signature->functions();f++){
    Signature::Symbol* fun = env.signature->getFunction(f);
    unsigned arity = fun->arity();
    int root = unionFind.root(offset_f[f]);
    unsigned rangeSort;
    if(!translate.find(root,rangeSort)){
      rangeSort=seen++;
      translate.insert(root,rangeSort);
    }

    if(arity==0){
#if DEBUG_SORT_INFERENCE
    cout << "adding " << f << " as constant for " << rangeSort << endl;
#endif
       sig->sortedConstants[rangeSort].push(Term::createConstant(f));
    }
    else{
#if DEBUG_SORT_INFERENCE
      cout << "recording " << f << " as function for " << rangeSort << endl;
#endif
       static DArray<TermList> args(8);
       args.ensure(arity);
       for(unsigned i=0;i<arity;i++){
         args[i].makeVar(0);
       }
       sig->sortedFunctions[rangeSort].push(Term::create(f,arity,args.begin()));
    }
      
  }

  for(unsigned s=0;s<sig->sorts;s++){

    if(sig->sortedConstants[s].size()==0 && sig->sortedFunctions[s].size()>0){
      unsigned fresh = env.signature->addFreshFunction(0,"fmbFreshConstant");
      sig->sortedConstants[s].push(Term::createConstant(fresh));
#if DEBUG_SORT_INFERENCE
      cout << "Adding fresh constant for sort "<<s<<endl;
#endif
    }

#if DEBUG_SORT_INFERENCE
    cout << "for sort " << s << " we have " << sig->sortedConstants[s].size() << " constants and ";
    cout << sig->sortedFunctions[s].size() << " functions" <<endl; 
#endif
  }

  return sig;

}

}
