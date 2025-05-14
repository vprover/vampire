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
 * @file SortInference.cpp
 * Implements class SortInference.
 *
 * NOTE: An important convention to remember is that when we have a DArray representing
 *       the _signature or grounding of a function the last argument is the return
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
#include "Lib/DHSet.hpp"

#include "Monotonicity.hpp"
#include "SortInference.hpp"

#define DEBUG_SORT_INFERENCE 0


namespace FMB
{

using namespace std;


/**
 * We assume this occurs *after* flattening so all literals are shallow
 *
 */
void SortInference::doInference()
{
  if(_ignoreInference){
#if DEBUG_SORT_INFERENCE
   cout << "Ignoring sort inference..." << endl;
#endif
    // setup the minimal signature

    // currently just collapse all sorts if _assumeMonotonic is on
    // so we're not compatable with GROUP

    unsigned dsorts =0;
    if(_assumeMonotonic){
      Stack<unsigned>* stack = new Stack<unsigned>();
      _sig->distinctToVampire.insert(dsorts,stack);
    }

    for(unsigned s=0;s<env.signature->typeCons();s++){
      if(env.getMainProblem()->getProperty()->usesSort(s) || env.signature->isNonDefaultCon(s)){
        if(_assumeMonotonic){
          _sig->distinctToVampire.get(dsorts)->push(s);
          Stack<unsigned>* stack = new Stack<unsigned>();
          stack->push(dsorts);
          _sig->vampireToDistinct.insert(s,stack);
          _sig->vampireToDistinctParent.insert(s,dsorts);
        }
        else{
          unsigned dsort = dsorts++;
          Stack<unsigned>* stack = new Stack<unsigned>();
          stack->push(s);
          _sig->distinctToVampire.insert(dsort,stack);
          stack = new Stack<unsigned>();
          stack->push(dsort);
          _sig->vampireToDistinct.insert(s,stack);
          _sig->vampireToDistinctParent.insert(s,dsort);
        }
      }
    }
    if(_assumeMonotonic){ dsorts++; }

    _sig->sorts = dsorts;
    _sig->distinctSorts = dsorts;
    //cout << "dsorts = "<<dsorts << endl;

    _sig->sortedConstants.ensure(dsorts);
    _sig->sortedFunctions.ensure(dsorts);
    _sig->sortBounds.ensure(dsorts);
    _sig->varEqSorts.ensure(dsorts);
    _sig->parents.ensure(dsorts);
    for(unsigned i=0;i<dsorts;i++){
      _sig->sortBounds[i]=UINT_MAX; // it might actually be better than this!
      _sig->parents[i]=i;
      _sig->varEqSorts[i]=i;
    }

    for(unsigned f=0;f<env.signature->functions();f++){
      if(f < _del_f.size() && _del_f[f]) continue;
      unsigned arity = env.signature->functionArity(f);
      OperatorType* ftype = env.signature->getFunction(f)->fnType();
      //cout << env.signature->functionName(f) << " : " << env.sorts->sortName(ftype->result()) << endl;;
      TermList resTypeT = ftype->result();
      unsigned resType = resTypeT.term()->functor();
      unsigned dsort = (*_sig->vampireToDistinct.get(resType))[0];
      //cout << env.signature->functionName(f) << " : " << dsort << endl;
      if(arity==0){
        _sig->sortedConstants[dsort].push(f);
      }else{
        _sig->sortedFunctions[dsort].push(f);
      }
    }

    // we need at least one constant for symmetry breaking
    for(unsigned s=0;s<env.signature->typeCons();s++){
      if(env.getMainProblem()->getProperty()->usesSort(s) || env.signature->isNonDefaultCon(s)){
        unsigned dsort = (*_sig->vampireToDistinct.get(s))[0];
        if(_sig->sortedConstants[dsort].isEmpty()){
          unsigned fresh = env.signature->addFreshFunction(0,"fmbFreshConstant");
          TermList sT = TermList(AtomicSort::createConstant(s));
          env.signature->getFunction(fresh)->setType(OperatorType::getConstantsType(sT));
          _sig->sortedConstants[dsort].push(fresh);
        }
      }
    }
    _sig->functionSignatures.ensure(env.signature->functions());
    _sig->predicateSignatures.ensure(env.signature->predicates());

    for(unsigned f=0;f<env.signature->functions();f++){
      if(f < _del_f.size() && _del_f[f]){
#if DEBUG_SORT_INFERENCE
       cout << "Skipping deleted function signature for " << env.signature->functionName(f) << endl;
#endif
        continue;
      }
      unsigned arity = env.signature->functionArity(f);
      OperatorType* ftype = env.signature->getFunction(f)->fnType();
      _sig->functionSignatures[f].ensure(arity+1);
      for(unsigned i=0;i<arity;i++){
        TermList argTypeT = ftype->arg(i);
        unsigned argType = argTypeT.term()->functor();
        _sig->functionSignatures[f][i]=(*_sig->vampireToDistinct.get(argType))[0];
      }
      TermList resTypeT = ftype->result();
      unsigned resType = resTypeT.term()->functor();
      _sig->functionSignatures[f][arity]=(*_sig->vampireToDistinct.get(resType))[0];
    }

    for(unsigned p=1;p<env.signature->predicates();p++){
      if(p < _del_p.size() && _del_p[p]) continue;
      unsigned arity = env.signature->predicateArity(p);
      OperatorType* ptype = env.signature->getPredicate(p)->predType();
      _sig->predicateSignatures[p].ensure(arity);
      for(unsigned i=0;i<arity;i++){
        TermList argTypeT = ptype->arg(i);
        unsigned argType = argTypeT.term()->functor();
        _sig->predicateSignatures[p][i]=(*_sig->vampireToDistinct.get(argType))[0];
      }
    }
    return;
  }

  // Monotoniticy Detection
  if(_usingMonotonicity){
    if(_print){
      cout << "Monotonicity information:" << endl;
      if(_assumeMonotonic){ cout << "Assuming all sorts monotonic due to translation" << endl; }
    }
    for(unsigned s=0;s<env.signature->typeCons();s++){
      if(env.getMainProblem()->getProperty()->usesSort(s) || env.signature->isNonDefaultCon(s)){
        bool monotonic = _assumeMonotonic;
        if(!monotonic){
          Monotonicity m(_clauses,s);
          auto monot_info = m.check();
          if (monot_info) {
            _monotonic_vampire_sorts.insert(s,monot_info);
          }
        }
        // if we didn't just add the monot_info, it should have been there already from the _assumeMonotonic branch
        ASS(!monotonic || _monotonic_vampire_sorts.findPtr(s))
        if(_print){
          if(monotonic && !_assumeMonotonic){
            cout << "Input sort " << env.signature->typeConName(s) << " is monotonic" << endl;
          }
        }
      }
    }
  }

  Array<unsigned> offset_f(env.signature->functions());
  Array<unsigned> offset_p(env.signature->predicates());

  unsigned count = 0;
  for(unsigned f=0; f < env.signature->functions();f++){
    if(f < _del_f.size() && _del_f[f]) continue;
    offset_f[f] = count;
    count += (1+env.signature->getFunction(f)->arity());
  }

#if DEBUG_SORT_INFERENCE
  //cout << "just functions count is " << count << endl;
#endif

  // skip 0 because it is always equality
  for(unsigned p=1; p < env.signature->predicates();p++){
    if(p < _del_p.size() && _del_p[p]) continue;
    offset_p[p] = count;
    count += (env.signature->getPredicate(p)->arity());
  }

#if DEBUG_SORT_INFERENCE
  cout << "count is " << count << ": this is the number of positions in the considered signature" << endl;
#endif

  if(count==0) count=1;

  IntUnionFind unionFind(count);
  ZIArray<unsigned> posEqualitiesOnPos;
  Stack<unsigned> varEqualityVampireSorts;
  DHMap<unsigned,unsigned> vampireSortMax;

  ClauseIterator cit = pvi(ClauseList::Iterator(_clauses));

  while(cit.hasNext()) {
    Clause* c = cit.next();

#if DEBUG_SORT_INFERENCE
    cout << "CLAUSE " << c->toString() << endl;
#endif

    unsigned cVarCnt = c->varCnt();
    Array<Stack<unsigned>> varPositions(cVarCnt);
    ZIArray<unsigned> varsWithPosEq(cVarCnt);
    IntUnionFind localUF(cVarCnt+1); // +1 to avoid it being 0.. last pos will not be used

    // When scanning the clause, keep info about whether it could be of the form C : X = t_1 | ... | X = t_n , where t_i may be a variable as well
    // (however, we can't have X \in \Vars(t_i): think of the unit clause X = f(X) which does not restrict the domain size to 1)
    // If the first literal is X = Y we remember X in v[0] and Y in v[1], subsequent literals will be different and only at most one candidate for "X" will remain
    // Any literal of the form X = nonvar reduces the num_vars_consdired to 1 or 0 (depending on whether X is possibly one of the two vars we keep track of)
    unsigned v[2];
    short unsigned num_vars_always_in_equalities = 3; // 3 means we are still open to the possibility of assigning both v1 and v2, but they are uninitialized at the moment

    for(unsigned i=0;i<c->length();i++) {
      Literal* l = (*c)[i];
      if(l->isEquality()) {
        // Positive equality means we might be in the { X = t_i } scenario
        if(l->isPositive()) {
          if (num_vars_always_in_equalities == 3) {         // the unitialized case
            num_vars_always_in_equalities = 0;
            for(unsigned i : {0,1}) {
              if (l->nthArgument(i)->isVar() && !l->nthArgument(1-i)->containsSubterm(*l->nthArgument(i))) {
                v[num_vars_always_in_equalities++] = l->nthArgument(i)->var();
              }
            }
          } else if (num_vars_always_in_equalities == 2) { // we are keeping track of 2 variables (we just saw "X"="Y" as the last (and first) literal and have v[0]=="X" and v[1]=="Y")
            // we assume duplicate literals have been eliminated, so at most one var will be kept after this stage
            for(unsigned i : {0,1}) {
              if (l->nthArgument(i)->isVar() && !l->nthArgument(1-i)->containsSubterm(*l->nthArgument(i))) {
                unsigned var = l->nthArgument(i)->var();
                if (v[0] == var) {
                  num_vars_always_in_equalities = 1;
                  break; // and we are done
                }
                if (v[1] == var) {
                  v[0] = var;
                  num_vars_always_in_equalities = 1;
                  break; // and we are done
                }
                // this side is a completely different var (than v[0] or v[1])
              }
            }
            if (num_vars_always_in_equalities == 2) {
              // we didn't succeed for either side, so it's over for this clause
              num_vars_always_in_equalities = 0;
            }
          } else if (num_vars_always_in_equalities == 1) {
            bool found = false;
            for(unsigned i : {0,1}) {
              if (l->nthArgument(i)->isVar() && !l->nthArgument(1-i)->containsSubterm(*l->nthArgument(i))) {
                if (v[0] == l->nthArgument(i)->var()) {
                  found = true;
                  break;
                }
                // this side is a different var than v[0]
              }
            }
            if (!found) {
              num_vars_always_in_equalities = 0;
            }
          }
        } else {
          num_vars_always_in_equalities = 0;
        }

        if(l->isTwoVarEquality()) {
          varEqualityVampireSorts.push(l->twoVarEqSort().term()->functor());
#if DEBUG_SORT_INFERENCE
          cout << "join X" << l->nthArgument(0)->var()<< " and X" << l->nthArgument(1)->var() << endl;
#endif
          localUF.doUnion(l->nthArgument(0)->var(),l->nthArgument(1)->var());
          if(l->polarity()) {
            varsWithPosEq[l->nthArgument(0)->var()]=1;
            varsWithPosEq[l->nthArgument(1)->var()]=1;
#if DEBUG_SORT_INFERENCE
            cout << "varsWithPosEq X" << l->nthArgument(0)->var() << endl;
            cout << "varsWithPosEq X" << l->nthArgument(1)->var() << endl;
#endif
          }
        } else {
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
          if(l->polarity()){
            posEqualitiesOnPos[n]=true;
          }
        }
      } else { // i.e., !(l->isEquality())
        num_vars_always_in_equalities = 0;

        unsigned n = offset_p[l->functor()];
        for(unsigned i=0;i<l->arity();i++){
          ASS(l->nthArgument(i)->isVar());
          varPositions[l->nthArgument(i)->var()].push(n+i);
#if DEBUG_SORT_INFERENCE
          cout << "push " << (n+i) << " for X" << l->nthArgument(i)->var() << endl;
#endif
        }
      }
    } // for(unsigned i=0;i<c->length();i++)

#if DEBUG_SORT_INFERENCE
   cout << "num_vars_always_in_equalities: " << num_vars_always_in_equalities << endl;
   for (unsigned i = 0; i < num_vars_always_in_equalities; i++) {
    cout << "X" << v[i] << endl;
   }
#endif
   if(0 < num_vars_always_in_equalities && num_vars_always_in_equalities <= 2) {
     // We don't actually need the variable, just need to know this is a X = t_i clause
     // If so, the first literal can be used to find the sort of X
     //  - if it is a two var equality we take the sort
     //  - otherwise, it will be of the form X = t and we get the sort of t
     unsigned sort = SortHelper::getEqualityArgumentSort((*c)[0]).term()->functor();
     unsigned max = c->length();
     unsigned old;
     // set the new max if it is smaller than an existing max
     if(!vampireSortMax.find(sort,old) || old > max){
       vampireSortMax.insert(sort,max);
     }
#if DEBUG_SORT_INFERENCE
     cout << "Max size for sort " << sort << " is " << c->length() << endl;
#endif
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
     // for each pair of stuff in the stack say that they are the same
     for(unsigned i=0;i<stack.size();i++){
       if(varsWithPosEq[v]){
#if DEBUG_SORT_INFERENCE
         cout << "recording posEq for " << stack[i] << endl;
#endif
         posEqualitiesOnPos[stack[i]]=true;
       }
       for(unsigned j=i+1;j<stack.size();j++){
#if DEBUG_SORT_INFERENCE
         cout << "doing union " << stack[i] << " and " << stack[j] << endl;
#endif
         unionFind.doUnion(stack[i],stack[j]);
       }
     }
   }

  } // while(cit.hasNext())

  unionFind.evalComponents();
  unsigned comps = unionFind.getComponentCount();

#if DEBUG_SORT_INFERENCE
  cout << comps << " components: this is the number of disjoint subsorts" << endl;
#endif

  _sig->sorts=comps;
  _sig->sortedConstants.ensure(comps);
  _sig->sortedFunctions.ensure(comps);

  // We will normalize the resulting sorts as we go
  // translate maps the components from union find to these new sorts
  DHMap<int,unsigned> translate;
  unsigned seen = 0;

  // True if there is a positive equality on a position with this sort
  // Later we will use this to promote sorts if _expandSubsorts is true

  // First check all of the predicate positions
  for(unsigned p=0;p<env.signature->predicates();p++){
    if(p < _del_p.size() && _del_p[p]) continue;
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
        _posEqualitiesOnSort[argSort]=true;
      }
    }
  }

  // Next check function positions for positive equalities
  // Also recorded the functions/constants for each sort
  for(unsigned f=0;f<env.signature->functions();f++){
    if(f < _del_f.size() && _del_f[f]) continue;

    unsigned offset = offset_f[f];
    unsigned arity = env.signature->functionArity(f);
    int root = unionFind.root(offset);
    unsigned rangeSort;
    if(!translate.find(root,rangeSort)){
      rangeSort=seen++;
      translate.insert(root,rangeSort);
    }

    if(posEqualitiesOnPos[offset]){
      _posEqualitiesOnSort[rangeSort]=true;
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
        _posEqualitiesOnSort[argSort]=true;
      }
    }
    if(arity==0){
#if DEBUG_SORT_INFERENCE
    cout << "adding " << env.signature->functionName(f) << " as constant for " << rangeSort << endl;
    //cout << "it is " << Term::createConstant(f)->toString() << endl;
#endif
       _sig->sortedConstants[rangeSort].push(f);
    }
    else{
#if DEBUG_SORT_INFERENCE
      cout << "recording " << env.signature->functionName(f) << " as function for " << rangeSort << endl;
#endif
       _sig->sortedFunctions[rangeSort].push(f);
    }
  }

  // Mainly for _printing sort information
  // We also add these dummy constants to sorts without them
  if(_print){
    cout << "Sort Inference information:" << endl;
    cout << comps << " inferred subsorts" << endl;
  }
  unsigned firstFreshConstant = UINT_MAX;
  DHMap<unsigned,unsigned> freshMap;
  for(unsigned s=0;s<comps;s++){
#if DEBUG_SORT_INFERENCE
    if(!_posEqualitiesOnSort[s]){ cout << "No positive equalities for subsort " << s << endl; }
#endif
    if(_sig->sortedConstants[s].size()==0 && _sig->sortedFunctions[s].size()>0){
      unsigned fresh = env.signature->addFreshFunction(0,"fmbFreshConstant");
      _sig->sortedConstants[s].push(fresh);
      freshMap.insert(fresh,s);
      if(firstFreshConstant==UINT_MAX) firstFreshConstant=fresh;
#if DEBUG_SORT_INFERENCE
      cout << "Adding fresh constant for subsort "<<s<<endl;
#endif
    }
    if((_print)){
      cout << "Subsort " << s << " has " << _sig->sortedConstants[s].size() << " constants and ";
      cout << _sig->sortedFunctions[s].size() << " functions" <<endl;
    }
  }

  _sig->sortBounds.ensure(comps);

  // Compute bounds on sorts
  for(unsigned s=0;s<comps;s++){
    // A sort is bounded if it contains only constants and has no positive equality
    if(_sig->sortedFunctions[s].size()==0 && !_posEqualitiesOnSort[s]){
      _sig->sortBounds[s]=_sig->sortedConstants[s].size();
      // If no constants pretend there is one
      if(_sig->sortBounds[s]==0){ _sig->sortBounds[s]=1;}
      if(_print){
        cout << "Found bound of " << _sig->sortBounds[s] << " for subsort " << s << endl;
#if DEBUG_SORT_INFERENCE
        if(_sig->sortBounds[s]==0){ cout << " (was 0)"; }
        cout << endl;
#endif
      }
    }
    else{
      _sig->sortBounds[s]=UINT_MAX;
    }
  }

  DArray<bool> parentSet(comps);
  for(unsigned i=0;i<comps;i++) parentSet[i]=false;

  _sig->parents.ensure(comps);
  _sig->functionSignatures.ensure(env.signature->functions());
  _sig->predicateSignatures.ensure(env.signature->predicates());

#if DEBUG_SORT_INFERENCE
  cout << "Setting function _signatures" << endl;
#endif

  // Now record the _signatures for functions
  for(unsigned f=0;f<env.signature->functions();f++){
    if(f < _del_f.size() && _del_f[f]) {
#if DEBUG_SORT_INFERENCE
    cout << "Skipping deleted function signature "  << env.signature->functionName(f) << endl;
#endif
      continue;
    }
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
      _sig->functionSignatures[f].ensure(1);
      _sig->functionSignatures[f][0]=srt;
#if DEBUG_SORT_INFERENCE
      cout << " fresh constant, so skipping" << endl;
#endif
      continue;
    }

    unsigned arity = env.signature->functionArity(f);
    _sig->functionSignatures[f].ensure(arity+1);
    int root = unionFind.root(offset_f[f]);
    unsigned rangeSort = translate.get(root);
#if DEBUG_SORT_INFERENCE
    cout << rangeSort << " <= ";
#endif
    _sig->functionSignatures[f][arity] = rangeSort;

    Signature::Symbol* fnSym = env.signature->getFunction(f);
    OperatorType* fnType = fnSym->fnType();
    if(parentSet[rangeSort]){
#if VDEBUG
      //cout << "FUNCTION " << env.signature->functionName(f) << endl;
      TermList vs = fnType->result();
      unsigned vampireSort = vs.term()->functor();
      unsigned ourSort = getDistinctSort(rangeSort,vampireSort,false);
      ASS_EQ(ourSort,_sig->parents[rangeSort]);
      ASS(_sig->distinctToVampire.find(ourSort));
      Stack<unsigned>::Iterator it(* _sig->distinctToVampire.get(ourSort));
      bool found=false;
      //cout << "<<<<" << rangeSort << endl;
      while(it.hasNext()){ unsigned vs = it.next(); if(vs==vampireSort) found=true;  }
      ASS_REP(found,Lib::Int::toString(rangeSort)+","+env.signature->typeConName(vampireSort));
#endif
    }
    else{
      parentSet[rangeSort]=true;
      TermList vs = fnType->result();
      unsigned vampireSort = vs.term()->functor();
      _sig->parents[rangeSort] = getDistinctSort(rangeSort,vampireSort);
    }


    for(unsigned i=0;i<arity;i++){
      int argRoot = unionFind.root(offset_f[f]+i+1);
      unsigned argSort = translate.get(argRoot);
#if DEBUG_SORT_INFERENCE
      cout << argSort << " ";
#endif
      _sig->functionSignatures[f][i] = argSort;
      if(parentSet[argSort]){
#if VDEBUG
      TermList vs = fnType->arg(i);
      unsigned vampireSort = vs.term()->functor();
      unsigned ourSort = getDistinctSort(argSort,vampireSort,false);
      ASS_EQ(ourSort,_sig->parents[argSort]);
      ASS(_sig->distinctToVampire.find(ourSort));
      Stack<unsigned>::Iterator it(* _sig->distinctToVampire.get(ourSort));
      bool found=false;
      while(it.hasNext()){ unsigned vs = it.next(); if(vs==vampireSort) found=true; }
      ASS_REP(found,Lib::Int::toString(argSort)+","+env.signature->typeConName(vampireSort));
#endif
      }
      else{
        parentSet[argSort]=true;
        TermList vs = fnType->arg(i);
        unsigned vampireSort = vs.term()->functor();
        _sig->parents[argSort] = getDistinctSort(argSort,vampireSort);
      }
    }
#if DEBUG_SORT_INFERENCE
   cout << "("<< offset_f[f] << ")"<< endl;
#endif
  } // for(unsigned f=0;f<env.signature->functions();f++)

#if DEBUG_SORT_INFERENCE
  cout << "Setting up fresh constant info" << endl;
#endif
  // Setting types for fresh constants
  for(unsigned f=firstFreshConstant;f<env.signature->functions();f++){
    unsigned srt = freshMap.get(f);
    unsigned dsrt = _sig->parents[srt];
    unsigned vsrt = (*_sig->distinctToVampire.get(dsrt))[0];
    TermList vsrtT = TermList(AtomicSort::createConstant(vsrt));
    env.signature->getFunction(f)->setType(OperatorType::getConstantsType(vsrtT));
    env.signature->getFunction(f)->markIntroduced();
  }

#if DEBUG_SORT_INFERENCE
  cout << "Setting predicate _signatures" << endl;
#endif
  // Remember to skip 0 as it is =
  for(unsigned p=1;p<env.signature->predicates();p++){
    if(p < _del_p.size() && _del_p[p]) continue;
#if DEBUG_SORT_INFERENCE
    cout << env.signature->predicateName(p) << " : ";
#endif
    //cout << env.signature->predicateName(p) <<" : ";
    unsigned arity = env.signature->predicateArity(p);
    // Now set _signatures
    _sig->predicateSignatures[p].ensure(arity);

    Signature::Symbol* prSym = env.signature->getPredicate(p);
    OperatorType* prType = prSym->predType();

    for(unsigned i=0;i<arity;i++){
      int argRoot = unionFind.root(offset_p[p]+i);
      unsigned argSort = translate.get(argRoot);
      _sig->predicateSignatures[p][i] = argSort;
      if(parentSet[argSort]){
#if VDEBUG
      TermList vs = prType->arg(i);
      unsigned vampireSort = vs.term()->functor();
      unsigned ourSort = getDistinctSort(argSort,vampireSort,false);
      ASS_EQ(ourSort,_sig->parents[argSort]);
      ASS(_sig->distinctToVampire.find(ourSort));
      Stack<unsigned>::Iterator it(* _sig->distinctToVampire.get(ourSort));
      bool found=false;
      while(it.hasNext()){ unsigned vs = it.next(); if(vs==vampireSort) found=true; }
      ASS_REP(found,Lib::Int::toString(argSort)+","+env.signature->typeConName(vampireSort));
#endif
      }
      else{
        parentSet[argSort]=true;
        TermList vs = prType->arg(i);
        unsigned vampireSort = vs.term()->functor();
        _sig->parents[argSort] = getDistinctSort(argSort,vampireSort);
      }
#if DEBUG_SORT_INFERENCE
      cout << argSort << " ";
#endif
    }
#if DEBUG_SORT_INFERENCE
   cout << "("<< offset_p[p] << ")"<< endl;
#endif
  }

  // sorting out variable equalities
  // first check that a sort exists for every variable equality we saw
  Stack<unsigned>::Iterator tvevsit(varEqualityVampireSorts);
  while(tvevsit.hasNext()){
    unsigned vsort = tvevsit.next();
    if(!_sig->vampireToDistinct.find(vsort)){
      // it's missing, let's make one
      unsigned dsort = _distinctSorts++;
      Stack<unsigned>* stack = new Stack<unsigned>();
      stack->push(vsort);
      _sig->distinctToVampire.insert(dsort,stack);
      stack = new Stack<unsigned>();
      stack->push(dsort);
      _sig->vampireToDistinct.insert(vsort,stack);
      _sig->vampireToDistinctParent.insert(vsort,dsort);
    }
  }
  // allocate an extra sort per disinct sort for variable equalities
  _sig->varEqSorts.ensure(_distinctSorts);
  _sig->sortBounds.expand(_sig->sorts+_distinctSorts);
  _sig->parents.expand(_sig->sorts+_distinctSorts);
  for(unsigned s=0;s<_distinctSorts;s++){
    _sig->varEqSorts[s] = _sig->sorts;
    _sig->sortBounds[_sig->sorts]=UINT_MAX;
    _sig->parents[_sig->sorts]=s;
    _sig->sorts++;
  }
  _sig->sortedConstants.expand(_sig->sorts);
  _sig->sortedFunctions.expand(_sig->sorts);

  _sig->distinctSorts = _distinctSorts;

  if(_print){
    if(_collapsed>0){ cout << "Collapsed " << _collapsed << " distinct sorts into 1 as they are monotonic" << endl;}
    cout << _sig->distinctSorts << " distinct sorts" << endl;
    for(unsigned s=0;s<_sig->distinctSorts;s++){
      unsigned children =0;
      std::string res="";
      for(unsigned i=0;i<_sig->sorts;i++){
        if(_sig->parents[i]==s){
          if(children>0) res+=",";
          res+=Lib::Int::toString(i);
          children++;
        }
      }
      cout << s << " has " << children << " inferred subsorts as members [" << res << "]" << endl;
    }
    cout << "Vampire to distinct sort mapping:" << endl;
    cout << "[";
    for(unsigned i=0;i<_sig->distinctSorts;i++){

      Stack<unsigned>* vs = _sig->distinctToVampire.get(i);
      if(vs->size()==1) cout << env.signature->typeConName((*vs)[0]);
      else cout << env.signature->typeConName((*vs)[0]) << "(+)";

      if(i==_sig->distinctSorts-1) cout << "]" << endl;
      else cout << ",";
    }
  }

  for(unsigned s=0;s<env.signature->typeCons();s++){
    if(env.getMainProblem()->getProperty()->usesSort(s) || env.signature->isNonDefaultCon(s)){
      // if sort is not here then it does not appear in signature (check)
      if(!_sig->vampireToDistinct.find(s)){ continue; }

      // make sure it has a parent
      if(!_sig->vampireToDistinctParent.find(s)){

        ASS(!_sig->vampireToDistinct.get(s)->isEmpty());

        if(_sig->vampireToDistinct.find(s)){
          _sig->vampireToDistinctParent.insert(s,(*_sig->vampireToDistinct.get(s))[0]);
        }
      }
      // add those constraints between children and parent
      unsigned parent = _sig->vampireToDistinctParent.get(s);
#if DEBUG_SORT_INFERENCE
      cout << "Parent " << parent << " for " << env.signature->typeConName(s) << endl;
#endif
      Stack<unsigned>::Iterator children(*_sig->vampireToDistinct.get(s));
      while(children.hasNext()){
        unsigned child = children.next();
        if(child==parent) continue;
#if DEBUG_SORT_INFERENCE
        cout << "Child " << child << " for " << env.signature->typeConName(s) << endl;
#endif
        _sort_constraints.push(make_pair(parent,child));
      }
    }
  }

  // Let the sorted signature know about the sort bounds found by the { X = t_i } scenario
  // To do this we need to map from vampire sorts to the sorts of the sorted signature
  // via the notion of distinct sort
  DHMap<unsigned,unsigned>::Iterator vmax(vampireSortMax);
  while(vmax.hasNext()){
    unsigned vsrt;
    unsigned max;
    vmax.next(vsrt,max);
    Stack<unsigned>* srts = _sig->vampireToDistinct.get(vsrt);
    Stack<unsigned>::Iterator it(*srts);
    while(it.hasNext()){
      unsigned dsrt = it.next();
      for(unsigned srt=0;srt<_sig->sorts;srt++){
        if(_sig->parents[srt] == dsrt){
          //cout << "(" << srt << "," << max << ")" << endl;
          _sig->sortBounds[srt] = min(_sig->sortBounds[srt],max);
        }
      }
    }
  }

}

unsigned SortInference::getDistinctSort(unsigned subsort, unsigned realVampireSort, bool createNew)
{
  // oink, oink
  static bool firstMonotonicSortSeen = false;
  static unsigned firstMonotonicSort = 0;
  static DHMap<unsigned,unsigned> ourDistinctSorts;

  unsigned vampireSort = realVampireSort;
  if(_expandSubsorts){
    if(!_posEqualitiesOnSort[subsort]){
      vampireSort = env.signature->typeCons()+subsort+1;
    }
  }

  unsigned ourSort;
  if(ourDistinctSorts.find(vampireSort,ourSort)){
    return ourSort;
  }
  //cout << "CREATE " << subsort << "," << env.sorts->sortName(realVampireSort) << endl;
  ASS(createNew);

  if(_monotonic_vampire_sorts.findPtr(vampireSort)){
    if(_collapsingMonotonicSorts){
      _collapsed++;
      if(firstMonotonicSortSeen){
        ourSort = ourDistinctSorts.get(firstMonotonicSort);
      }
      else{
        firstMonotonicSortSeen=true;
        firstMonotonicSort = vampireSort;
        ourSort = _distinctSorts++;
      }
    }
    else{
      ourSort = _distinctSorts++;
    }
    _sig->monotonicSorts[ourSort]=true;
  }
  else {
    ourSort = _distinctSorts++;
  }

  ourDistinctSorts.insert(vampireSort,ourSort);

  if(!_sig->distinctToVampire.find(ourSort)){
    _sig->distinctToVampire.insert(ourSort,new Stack<unsigned>());
  }
  _sig->distinctToVampire.get(ourSort)->push(realVampireSort);

  if(!_sig->vampireToDistinct.find(realVampireSort)){
    _sig->vampireToDistinct.insert(realVampireSort,new Stack<unsigned>());
  }
  _sig->vampireToDistinct.get(realVampireSort)->push(ourSort);
  if(vampireSort == realVampireSort){
    _sig->vampireToDistinctParent.insert(vampireSort,ourSort);
  }

  //cout << "RET " << vampireSort << " to " << ourSort << endl;

  return ourSort;
}

}
