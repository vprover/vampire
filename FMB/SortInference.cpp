/**
 * @file SortInference.cpp
 * Implements class SortInference.
 *
 * NOTE: An important convention to remember is that when we have a DArray representing
 *       the signature or grounding of a function the last argument is the return
 *       so array[arity] is return and array[i] is the ith argument of the function
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
#include "Lib/List.hpp"

#include "Monotonicity.hpp"
#include "SortInference.hpp"

#define DEBUG_SORT_INFERENCE 0


namespace FMB 
{


/**
 * We assume this occurs *after* flattening so all literals are shallow
 *
 */
SortedSignature* SortInference::apply(ClauseList* clauses,
                                      DArray<unsigned> del_f,DArray<unsigned> del_p)
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

  ZIArray<unsigned> posEqualitiesOnPos(count);
  DHSet<unsigned> vampireSortsWithTwoVarEqs;

  IntUnionFind unionFind(count);

  ClauseIterator cit = pvi(ClauseList::Iterator(clauses));

  while(cit.hasNext()){
   Clause* c = cit.next();
  
#if DEBUG_SORT_INFERENCE
   //cout << "CLAUSE " << c->toString() << endl;
#endif

   Array<Stack<unsigned>> varPositions(c->varCnt());
   ZIArray<unsigned> varsWithPosEq(c->varCnt());
   ZIArray<unsigned> varsNotOnlyInVarEq(c->varCnt());
   DHMap<unsigned,unsigned> varInVarEqToVampireSort;
   IntUnionFind localUF(c->varCnt()+1); // +1 to avoid it being 0.. last pos will not be used
   for(unsigned i=0;i<c->length();i++){
     Literal* l = (*c)[i];
     if(l->isEquality()){
       if(l->isTwoVarEquality()){
#if DEBUG_SORT_INFERENCE
         //cout << "join X" << l->nthArgument(0)->var()<< " and X" << l->nthArgument(1)->var() << endl;
#endif
         localUF.doUnion(l->nthArgument(0)->var(),l->nthArgument(1)->var());
         if(l->polarity()){
           varsWithPosEq[l->nthArgument(0)->var()]=1;
           varsWithPosEq[l->nthArgument(1)->var()]=1;
         }
         varInVarEqToVampireSort.insert(l->nthArgument(0)->var(),l->twoVarEqSort());
         varInVarEqToVampireSort.insert(l->nthArgument(1)->var(),l->twoVarEqSort());
         
       }else{
         ASS(!l->nthArgument(0)->isVar());
         ASS(l->nthArgument(1)->isVar());
         Term* t = l->nthArgument(0)->term();

         unsigned f = t->functor();
         unsigned n = offset_f[f];
         varPositions[l->nthArgument(1)->var()].push(n);
         varsNotOnlyInVarEq[l->nthArgument(1)->var()] = 1;
#if DEBUG_SORT_INFERENCE
         //cout << "push " << n << " for X" << l->nthArgument(1)->var() << endl;
#endif
         for(unsigned i=0;i<t->arity();i++){
           ASS(t->nthArgument(i)->isVar());
           varPositions[t->nthArgument(i)->var()].push(n+1+i);
           varsNotOnlyInVarEq[t->nthArgument(i)->var()] = 1;
#if DEBUG_SORT_INFERENCE
           //cout << "push " << (n+1+i) << " for X" << t->nthArgument(i)->var() << endl;
#endif
         }
         if(l->polarity()){
           posEqualitiesOnPos[n]=true;
         }
       }
     }
     else{
       unsigned n = offset_p[l->functor()];
       for(unsigned i=0;i<l->arity();i++){
           ASS(l->nthArgument(i)->isVar());
           varPositions[l->nthArgument(i)->var()].push(n+i);
           varsNotOnlyInVarEq[l->nthArgument(i)->var()] = 1;
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
       if(varsWithPosEq[v]){
#if DEBUG_SORT_INFERENCE
         //cout << "recording posEq for " << stack[i] << endl;
#endif
         posEqualitiesOnPos[stack[i]]=true;
       }
       for(unsigned j=i+1;j<stack.size();j++){
#if DEBUG_SORT_INFERENCE
         //cout << "doing union " << stack[i] << " and " << stack[j] << endl;
#endif
         unionFind.doUnion(stack[i],stack[j]);
       }
     }
   }
   for(unsigned v=0;v<c->varCnt() ; v++){
     if(!varsNotOnlyInVarEq[v]){
       vampireSortsWithTwoVarEqs.insert(varInVarEqToVampireSort.get(v));
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

  // We will normalize the resulting sorts as we go
  // translate maps the components from union find to these new sorts
  DHMap<int,unsigned> translate;
  unsigned seen = 0;

  // True if there is a positive equality on a position with this sort
  ZIArray<bool> posEqualitiesOnSort(comps); 

  // First check all of the predicate positions
  for(unsigned p=0;p<env.signature->predicates();p++){
    if(p < del_p.size() && del_p[p]) continue;
    unsigned offset = offset_p[p];
    unsigned arity = env.signature->predicateArity(p);
    for(unsigned i=0;i<arity;i++){
      unsigned arg_offset = offset+i;
      int argRoot = unionFind.root(arg_offset);
      unsigned argSort;
      if(!translate.find(argRoot,argSort)){
        argSort=seen++;
        translate.insert(argRoot,argSort);
      }
      if(posEqualitiesOnPos[arg_offset]){
        posEqualitiesOnSort[argSort]=true;
      }
    }
  }

  // Next check function positions for positive equalities
  // Also recorded the functions/constants for each sort
  for(unsigned f=0;f<env.signature->functions();f++){
    if(f < del_f.size() && del_f[f]) continue;

    unsigned offset = offset_f[f];
    unsigned arity = env.signature->functionArity(f); 
    int root = unionFind.root(offset);
    unsigned rangeSort;
    if(!translate.find(root,rangeSort)){
      rangeSort=seen++;
      translate.insert(root,rangeSort);
    }

    if(posEqualitiesOnPos[offset]){
      posEqualitiesOnSort[rangeSort]=true;
    }
    for(unsigned i=0;i<arity;i++){
      unsigned arg_offset = offset+i+1;
      int argRoot = unionFind.root(arg_offset);
      unsigned argSort;
      if(!translate.find(argRoot,argSort)){
        argSort=seen++;
        translate.insert(argRoot,argSort);
      }
      if(posEqualitiesOnPos[arg_offset]){
        posEqualitiesOnSort[argSort]=true;
      }
    }
    if(arity==0){
#if DEBUG_SORT_INFERENCE
    cout << "adding " << env.signature->functionName(f) << " as constant for " << rangeSort << endl;
    //cout << "it is " << Term::createConstant(f)->toString() << endl;
#endif
       sig->sortedConstants[rangeSort].push(f);
    }
    else{
#if DEBUG_SORT_INFERENCE
      cout << "recording " << env.signature->functionName(f) << " as function for " << rangeSort << endl;
#endif
       sig->sortedFunctions[rangeSort].push(f);
    }

  }

  // Mainly for printing sort information
  // We also add these dummy constants to sorts without them
  if(env.options->mode()!=Options::Mode::SPIDER){
    cout << "Sort Inference information:" << endl;
    cout << comps << " inferred sorts" << endl;
  }
  unsigned firstFreshConstant = UINT_MAX;
  DHMap<unsigned,unsigned> freshMap;
  for(unsigned s=0;s<comps;s++){
    if(sig->sortedConstants[s].size()==0 && sig->sortedFunctions[s].size()>0){
      unsigned fresh = env.signature->addFreshFunction(0,"fmbFreshConstant");
      sig->sortedConstants[s].push(fresh);
      freshMap.insert(fresh,s);
      if(firstFreshConstant==UINT_MAX) firstFreshConstant=fresh;
#if DEBUG_SORT_INFERENCE
      cout << "Adding fresh constant for sort "<<s<<endl;
#endif
    }
    if((env.options->mode()!=Options::Mode::SPIDER)){
      cout << "Sort " << s << " has " << sig->sortedConstants[s].size() << " constants and ";
      cout << sig->sortedFunctions[s].size() << " functions" <<endl;
    }
  }


  sig->sortBounds.ensure(comps);

  // Compute bounds on sorts
  for(unsigned s=0;s<comps;s++){
    // A sort is bounded if it contains only constants and has no positive equality
    if(sig->sortedFunctions[s].size()==0 && !posEqualitiesOnSort[s]){
      sig->sortBounds[s]=sig->sortedConstants[s].size();
      // If no constants pretend there is one
      if(sig->sortBounds[s]==0){ sig->sortBounds[s]=1;}
      if(env.options->mode()!=Options::Mode::SPIDER){
        cout << "Found bound of " << sig->sortBounds[s] << " for sort " << s << endl;
#if DEBUG_SORT_INFERENCE
        if(sig->sortBounds[s]==0){ cout << " (was 0)"; }
        cout << endl;
#endif
      }
    }
    else{
      sig->sortBounds[s]=UINT_MAX;
    }
    //if(s==3){
      //cout << "Forcing all bounds to max for " << s << endl;
      //bounds[s] = UINT_MAX;
    //}
  }

  DArray<bool> parentSet(comps);
  for(unsigned i=0;i<comps;i++) parentSet[i]=false;

  sig->parents.ensure(comps);
  sig->functionSignatures.ensure(env.signature->functions());
  sig->predicateSignatures.ensure(env.signature->predicates());

  unsigned distinctSorts = 0;
  DHMap<unsigned,unsigned> ourDistinctSorts; 

#if DEBUG_SORT_INFERENCE
  cout << "Setting function signatures" << endl;
#endif

  // Now record the signatures for functions
  for(unsigned f=0;f<env.signature->functions();f++){
    if(f < del_f.size() && del_f[f]) continue;
#if DEBUG_SORT_INFERENCE
    cout << env.signature->functionName(f) << " : ";
#endif
    // fresh constants are introduced for sorts with no constants
    // but that have function symbols, therefore these sorts cannot
    // be bounded 
    // We need to treat them specially as they are functions that are added
    // after we do sort inference (so offsets/positions do not apply)
    if(f >= firstFreshConstant){
      unsigned srt = freshMap.get(f);
      sig->functionSignatures[f].ensure(1);
      sig->functionSignatures[f][0]=srt;
#if DEBUG_SORT_INFERENCE
      cout << " fresh constant, so skipping" << endl;
#endif
      continue;
    }

    unsigned arity = env.signature->functionArity(f);
    sig->functionSignatures[f].ensure(arity+1);
    int root = unionFind.root(offset_f[f]);
    unsigned rangeSort = translate.get(root);
#if DEBUG_SORT_INFERENCE
    cout << rangeSort << " <= ";
#endif
    sig->functionSignatures[f][arity] = rangeSort;

    Signature::Symbol* fnSym = env.signature->getFunction(f);
    FunctionType* fnType = fnSym->fnType();
    if(parentSet[rangeSort]){
#if VDEBUG
      unsigned vampireSort = fnType->result();
      unsigned ourSort;
      ASS(ourDistinctSorts.find(vampireSort,ourSort));
      ASS_EQ(ourSort,sig->parents[rangeSort]);
#endif
    }
    else{
      parentSet[rangeSort]=true;
      unsigned vampireSort = fnType->result();
      unsigned ourSort; 
      if(!ourDistinctSorts.find(vampireSort,ourSort)){
        ourSort = distinctSorts++;
        ourDistinctSorts.insert(vampireSort,ourSort);
        if(!sig->distinctToVampire.find(ourSort)){ sig->distinctToVampire.insert(ourSort,new Stack<unsigned>());}
        sig->distinctToVampire.get(ourSort)->push(vampireSort);
        sig->vampireToDistinct.insert(vampireSort,ourSort);
      }
      sig->parents[rangeSort] = ourSort;
      //cout << "set parent of " << rangeSort << " to " << ourSort << endl;
    }


    for(unsigned i=0;i<arity;i++){
      int argRoot = unionFind.root(offset_f[f]+i+1);
      unsigned argSort = translate.get(argRoot);
#if DEBUG_SORT_INFERENCE
      cout << argSort << " ";
#endif
      sig->functionSignatures[f][i] = argSort;
      if(parentSet[argSort]){
#if VDEBUG
      unsigned vampireSort = fnType->arg(i);
      unsigned ourSort;
      ASS(ourDistinctSorts.find(vampireSort,ourSort));
      ASS_EQ(ourSort,sig->parents[argSort]);
#endif
      }
      else{
        parentSet[argSort]=true;
        unsigned vampireSort = fnType->arg(i);
        unsigned ourSort;
        if(!ourDistinctSorts.find(vampireSort,ourSort)){
          ourSort = distinctSorts++;
          ourDistinctSorts.insert(vampireSort,ourSort);
          if(!sig->distinctToVampire.find(ourSort)){ sig->distinctToVampire.insert(ourSort,new Stack<unsigned>());}
          sig->distinctToVampire.get(ourSort)->push(vampireSort);
          sig->vampireToDistinct.insert(vampireSort,ourSort);
        }
        sig->parents[argSort] = ourSort;
        //cout << "set parent of " << argSort << " to " << ourSort << endl;
      }
    }
#if DEBUG_SORT_INFERENCE
   cout << "("<< offset_f[f] << ")"<< endl;
#endif
  }

  // Setting types for fresh constants
  for(unsigned f=firstFreshConstant;f<env.signature->functions();f++){
    unsigned srt = freshMap.get(f);
    unsigned dsrt = sig->parents[srt];
    unsigned vsrt = (*sig->distinctToVampire.get(dsrt))[0];
    env.signature->getFunction(f)->setType(new FunctionType(vsrt));
    env.signature->getFunction(f)->markIntroduced();
  }

#if DEBUG_SORT_INFERENCE
  cout << "Setting predicate signatures" << endl;
#endif

  // Remember to skip 0 as it is =
  for(unsigned p=1;p<env.signature->predicates();p++){
    if(p < del_p.size() && del_p[p]) continue;
#if DEBUG_SORT_INFERENCE
    cout << env.signature->predicateName(p) << " : ";
#endif
    //cout << env.signature->predicateName(p) <<" : "; 
    unsigned arity = env.signature->predicateArity(p);
    // Now set signatures 
    sig->predicateSignatures[p].ensure(arity);

    Signature::Symbol* prSym = env.signature->getPredicate(p);
    PredicateType* prType = prSym->predType();

    for(unsigned i=0;i<arity;i++){
      int argRoot = unionFind.root(offset_p[p]+i);
      unsigned argSort = translate.get(argRoot);
      sig->predicateSignatures[p][i] = argSort;
      if(parentSet[argSort]){
#if VDEBUG
      unsigned vampireSort = prType->arg(i);
      unsigned ourSort;
      ASS(ourDistinctSorts.find(vampireSort,ourSort));
      ASS_EQ(ourSort,sig->parents[argSort]);
#endif
      }
      else{
        parentSet[argSort]=true;
        unsigned vampireSort = prType->arg(i);
        unsigned ourSort;
        if(!ourDistinctSorts.find(vampireSort,ourSort)){
          ourSort = distinctSorts++;
          ourDistinctSorts.insert(vampireSort,ourSort);
          if(!sig->distinctToVampire.find(ourSort)){ sig->distinctToVampire.insert(ourSort,new Stack<unsigned>());}
          sig->distinctToVampire.get(ourSort)->push(vampireSort);
          sig->vampireToDistinct.insert(vampireSort,ourSort);
        }
        sig->parents[argSort] = ourSort;
        //cout << "set parent of " << argSort << " to " << ourSort << endl;
      }
#if DEBUG_SORT_INFERENCE
      cout << argSort << " ";
#endif
    }    
#if DEBUG_SORT_INFERENCE
   cout << "("<< offset_p[p] << ")"<< endl;
#endif
  }

  sig->distinctSorts = distinctSorts;

  for(unsigned s=0;s<env.sorts->sorts();s++){
    if(ourDistinctSorts.find(s)){
      Monotonicity m(clauses,s);
      if(m.check()){
        cout << "vampire sort " << s << " is monotonic" << endl;
      }
      else{
        cout << "vampire sort " << s << " is not monotonic" << endl;
      }
    }
  }

  if(env.options->mode()!=Options::Mode::SPIDER){
    cout << sig->distinctSorts << " distinct sorts" << endl;
    for(unsigned s=0;s<sig->distinctSorts;s++){
      unsigned children =0;
      vstring res="";
      for(unsigned i=0;i<sig->sorts;i++){ 
        if(sig->parents[i]==s){
          if(children>0) res+=",";
          res+=Lib::Int::toString(i);
          children++; 
        }
      }
      cout << s << " has " << children << " inferred sorts as members [" << res << "]" << endl;
    }
  }


  return sig;

}

}
