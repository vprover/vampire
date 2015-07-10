/**
 * @file SortInference.cpp
 * Implements class SortInference.
 */

#include "Shell/Options.hpp"

#include "Kernel/Term.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"

#include "Lib/Array.hpp"
#include "Lib/DArray.hpp"
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
SortedSignature* SortInference::apply(ClauseIterator cit,DArray<unsigned> del_f,DArray<unsigned> del_p)
{
  CALL("SortInference::run");

  Array<unsigned> offset_f(env.signature->functions());
  Array<unsigned> offset_p(env.signature->predicates());

  unsigned count = 0;
  for(unsigned f=0; f < env.signature->functions();f++){
    if(del_f[f]) continue;
    offset_f[f] = count;
    count += (1+env.signature->getFunction(f)->arity());
  }

#if DEBUG_SORT_INFERENCE
  //cout << "just functions count is " << count << endl;
#endif

  // skip 0 because it is always equality
  for(unsigned p=1; p < env.signature->predicates();p++){
    if(del_p[p]) continue;
    offset_p[p] = count;
    count += (env.signature->getPredicate(p)->arity());
  }

#if DEBUG_SORT_INFERENCE
  cout << "count is " << count << endl;
#endif

  if(count==0) count=1;

  DArray<unsigned> posEqualitiesOnFunc(env.signature->functions());

  IntUnionFind unionFind(count);

  while(cit.hasNext()){
   Clause* c = cit.next();
  
   //cout << "CLAUSE " << c->toString() << endl;

   Array<Stack<unsigned>> varPositions(c->varCnt());
   IntUnionFind localUF(c->varCnt()+1); // +1 to avoid it being 0.. last pos will not be used
   for(unsigned i=0;i<c->length();i++){
     Literal* l = (*c)[i];
     if(l->isEquality()){
       if(l->isTwoVarEquality()){
#if DEBUG_SORT_INFERENCE
         //cout << "join X" << l->nthArgument(0)->var()<< " and X" << l->nthArgument(1)->var() << endl;
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
         //cout << "push " << n << " for X" << l->nthArgument(1)->var() << endl;
#endif
         for(unsigned i=0;i<t->arity();i++){
           ASS(t->nthArgument(i)->isVar());
           varPositions[t->nthArgument(i)->var()].push(n+1+i);
#if DEBUG_SORT_INFERENCE
           //cout << "push " << (n+1+i) << " for X" << t->nthArgument(i)->var() << endl;
#endif
         }
         if(l->polarity()){
           posEqualitiesOnFunc[f]=true;
         }
       }
     }
     else{
       unsigned n = offset_p[l->functor()];
       for(unsigned i=0;i<l->arity();i++){
           ASS(l->nthArgument(i)->isVar());
           varPositions[l->nthArgument(i)->var()].push(n+i);
#if DEBUG_SORT_INFERENCE
           //cout << "push " << (n+i) << " for X" << l->nthArgument(i)->var() << endl;
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
         //cout << "doing union " << stack[i] << " and " << stack[j] << endl;
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

  DArray<bool> posEqualitiesOnSort(comps); 

  for(unsigned f=0;f<env.signature->functions();f++){
    if(del_f[f]) continue;

    unsigned arity = env.signature->functionArity(f); 
    int root = unionFind.root(offset_f[f]);
    unsigned rangeSort;
    if(!translate.find(root,rangeSort)){
      rangeSort=seen++;
      translate.insert(root,rangeSort);
    }

    if(posEqualitiesOnFunc[f]){
      posEqualitiesOnSort[rangeSort]=true;
    }

    if(arity==0){
#if DEBUG_SORT_INFERENCE
    cout << "adding " << f << " as constant for " << rangeSort << endl;
    //cout << "it is " << Term::createConstant(f)->toString() << endl;
#endif
       sig->sortedConstants[rangeSort].push(f);
    }
    else{
#if DEBUG_SORT_INFERENCE
      cout << "recording " << f << " as function for " << rangeSort << endl;
#endif
       sig->sortedFunctions[rangeSort].push(f);
    }

  }

  if(env.options->mode()!=Options::Mode::SPIDER){
    cout << "Sort Inference information:" << endl;
  }

  for(unsigned s=0;s<comps;s++){

    if(sig->sortedConstants[s].size()==0 && sig->sortedFunctions[s].size()>0){
      unsigned fresh = env.signature->addFreshFunction(0,"fmbFreshConstant");
      sig->sortedConstants[s].push(fresh);
#if DEBUG_SORT_INFERENCE
      cout << "Adding fresh constant for sort "<<s<<endl;
#endif
    }
    if((env.options->mode()!=Options::Mode::SPIDER) && sig->sortedConstants[s].size()>0){
      cout << "Sort " << s << " has " << sig->sortedConstants[s].size() << " constants and ";
      cout << sig->sortedFunctions[s].size() << " functions" <<endl;
    }
  }

  sig->functionBounds.ensure(env.signature->functions());
  sig->predicateBounds.ensure(env.signature->predicates());

  DArray<unsigned> bounds(comps);

  // Compute bounds on sorts
  for(unsigned s=0;s<comps;s++){
    if(sig->sortedFunctions[s].size()==0 && !posEqualitiesOnSort[s]){
      bounds[s]=sig->sortedConstants[s].size();
      // If no constants pretend there is one
      if(bounds[s]==0){ bounds[s]=1;}
#if DEBUG_SORT_INFERENCE
      cout << "Bounding sort " << s << " to " << bounds[s] << endl;
#endif
    }
    else{
      bounds[s]=UINT_MAX;
    }
  }

#if DEBUG_SORT_INFERENCE
  cout << "Setting function bounds" << endl;
#endif

  // Now set bounds for functions
  for(unsigned f=0;f<env.signature->functions();f++){
    if(f < del_f.size() && del_f[f]) continue;
#if DEBUG_SORT_INFERENCE
    cout << env.signature->functionName(f) << " : ";
#endif
    unsigned arity = env.signature->functionArity(f);
    sig->functionBounds[f].ensure(arity+1);
    int root = unionFind.root(offset_f[f]);
    unsigned rangeSort = translate.get(root);
#if DEBUG_SORT_INFERENCE
    cout << rangeSort << " ";
#endif
    sig->functionBounds[f][0] = bounds[rangeSort];
    for(unsigned i=0;i<arity;i++){
      int argRoot = unionFind.root(offset_f[f]+i+1);
      unsigned argSort;
      if(!translate.find(argRoot,argSort)){
        argSort=seen++;
        translate.insert(argRoot,argSort);
      }
#if DEBUG_SORT_INFERENCE
      cout << argSort << " ";
#endif
      sig->functionBounds[f][i+1] = bounds[argSort];
    }
#if DEBUG_SORT_INFERENCE
   cout << "("<< offset_f[f] << ")"<< endl;
#endif
  }

#if DEBUG_SORT_INFERENCE
  cout << "Setting predicate bounds" << endl;
#endif

  // For predicates we just record bounds
  // Remember to skip 0 as it is =
  for(unsigned p=1;p<env.signature->predicates();p++){
    if(p < del_p.size() && del_p[p]) continue;
    //cout << env.signature->predicateName(p) <<" : "; 
    unsigned arity = env.signature->predicateArity(p);
    // Now set bounds
    sig->predicateBounds[p].ensure(arity);
    for(unsigned i=0;i<arity;i++){
      int argRoot = unionFind.root(offset_p[p]+i);
      unsigned argSort;
      if(!translate.find(argRoot,argSort)){
        argSort=seen++;
        translate.insert(argRoot,argSort);
      }
      //cout << argRoot << " ";
      sig->predicateBounds[p][i] = bounds[argSort];
    }    
    //cout << "("<< offset_p[p] << ")"<< endl;
  }

  return sig;

}

}
