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
 * @file Instantiation.cpp
 * Implements class Instantiation.
 * @author Giles
 */

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/VirtualIterator.hpp"
#include "Lib/DArray.hpp"
#include "Lib/Set.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/OperatorType.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Substitution.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Theory.hpp"
#include "Kernel/TermIterators.hpp"

#include "Shell/Statistics.hpp"

#include "Instantiation.hpp"

namespace Inferences
{

using namespace Lib;
using namespace Kernel;
/*
struct IntToIntTermFn
{
  IntToIntTermFn(){}
  Term* operator()(unsigned int i)
  {
    return theory->representConstant(IntegerConstantType(i));
  }
};
struct IntToRatTermFn
{
  IntToRatTermFn(){}
  Term* operator()(unsigned int i)
  {
    return theory->representConstant(RationalConstantType(i,1));
  }
};
struct IntToRealTermFn
{
  IntToRealTermFn(){}
  Term* operator()(unsigned int i)
  {
    return theory->representConstant(RealConstantType(RationalConstantType(i,1)));
  }
};

struct InvertNumber
{
  InvertNumber();
  unsigned operator()(unsigned int i){ return -i; }
};

void Instantiation::init(){
  CALL("Instantiation::init");
    Set<Term*>* intSet = new Set<Term*>();
    Set<Term*>* ratSet = new Set<Term*>();
    Set<Term*>* realSet = new Set<Term*>();
   

    intSet->insertFromIterator(pvi(getMappingIterator(getRangeIterator(0u,10u),IntToIntTermFn())));
    intSet->insertFromIterator(pvi(getMappingIterator(getMappingIterator(getRangeIterator(0u,10u),InvertNumber()),IntToIntTermFn())));
    ratSet->insertFromIterator(pvi(getMappingIterator(getRangeIterator(0u,10u),IntToRatTermFn())));
    ratSet->insertFromIterator(pvi(getMappingIterator(getMappingIterator(getRangeIterator(0u,10u),InvertNumber()),IntToRatTermFn())));
    realSet->insertFromIterator(pvi(getMappingIterator(getRangeIterator(0u,10u),IntToRealTermFn())));
    realSet->insertFromIterator(pvi(getMappingIterator(getMappingIterator(getRangeIterator(0u,10u),InvertNumber()),IntToRealTermFn())));

    sorted_candidates.insert(Sorts::SRT_INTEGER,intSet);
    sorted_candidates.insert(Sorts::SRT_RATIONAL,ratSet);
    sorted_candidates.insert(Sorts::SRT_REAL,realSet);

  }
*/

/**
 * Let's still store the per-sort constants from the problem
 *
 */
void Instantiation::registerClause(Clause* cl)
{
  CALL("Instantiation::registerClause");
  ASS(cl);

  //cout << "register " << cl->toString() << endl;

  Clause::Iterator cit(*cl);
  while(cit.hasNext()){
    Literal* lit = cit.next();
    SubtermIterator it(lit);
    while(it.hasNext()){
      TermList t = it.next();
      if(t.isTerm() && t.term()->ground()){
        TermList sort;
        if(SortHelper::tryGetResultSort(t,sort)){
          if(sort==AtomicSort::defaultSort()) continue;
          Set<Term*>* cans_check=0;
          Stack<Term*>* cans=0;
          if(sorted_candidates.isEmpty() || !sorted_candidates.find(sort,cans)){
            cans_check = new Set<Term*>();
            cans = new Stack<Term*>();
            sorted_candidates.insert(sort,cans);
            sorted_candidates_check.insert(sort,cans_check);
          }
          else{ ALWAYS(sorted_candidates_check.find(sort,cans_check)); }
          ASS(cans_check && cans);
          // cout << "For sort " << sort << " there are " << cans->size() << " cans" <<endl;
          if(!cans_check->contains(t.term())){
            cans_check->insert(t.term());
            cans->push(t.term());
          }
        }
      }
    }
  }

}

/**
 * The idea is to find terms that will make a literal in the clause true or false
 *
 */
void Instantiation::tryMakeLiteralFalse(Literal* lit, Stack<Substitution>& subs)
{
  CALL("Instantiation::tryMakeLiteralFalse");

  if(theory->isInterpretedPredicate(lit->functor())){
    Interpretation itp = theory->interpretPredicate(lit);
    //unsigned sort = theory->getOperationSort(interpretation);

    //TODO, very limited consideration, expand
    if (itp == Theory::EQUAL || itp == Theory::INT_LESS || itp == Theory::RAT_LESS || itp == Theory::REAL_LESS) {
      TermList* left = lit->nthArgument(0); TermList* right = lit->nthArgument(1);
      unsigned var;
      Term* t = 0;
      if(left->isVar() && !right->isVar()){
       t = right->term();
       var = left->var();
      }
      if(right->isVar() && !left->isVar()){
       t = left->term();
       var = right->var();
      }
      if(t){
        // do occurs check
        VariableIterator vit(t);
        while(vit.hasNext()) if(vit.next().var()==var) return;

        // we are okay
        Substitution s1;
        s1.bind(var,t);
        subs.push(s1);
        if(lit->polarity()){
         t = tryGetDifferentValue(t);
         if(t){
           Substitution s2;
           s2.bind(var,t);
           subs.push(s2);
         }
        }
      }
    }
    // TODO cover other cases ...
  }
}

Term* Instantiation::tryGetDifferentValue(Term* t)
{
  CALL("Instantiation::tryGetDifferentValue");

  TermList sort = SortHelper::getResultSort(t);

  try {
        if(sort == AtomicSort::intSort()){
              IntegerConstantType constant;
              if(theory->tryInterpretConstant(t,constant)){
                return theory->representConstant(constant+1);
              }
        } else if(sort == AtomicSort::rationalSort()){
              RationalConstantType constant;
              RationalConstantType one(1,1);
              if(theory->tryInterpretConstant(t,constant)){
                return theory->representConstant(constant+one);
              }
        } else if(sort == AtomicSort::realSort()){
              RealConstantType constant;
              RealConstantType one(RationalConstantType(1,1));
              if(theory->tryInterpretConstant(t,constant)){
                return theory->representConstant(constant+one);
              }
        }
  } catch (ArithmeticException&) {
    // return 0 as well
  }

  return 0;
}

VirtualIterator<Term*> Instantiation::getCandidateTerms(Clause* cl, unsigned var,TermList sort)
{
  CALL("Instantiation::getCandidateTerms");

  Stack<Term*>* cans=0;
  VirtualIterator<Term*> res = VirtualIterator<Term*>::getEmpty();
  if(sorted_candidates.find(sort,cans) && cans->size()){
    res = pvi(Stack<Term*>::Iterator(*cans));
  }
  return res; 
}

class Instantiation::AllSubstitutionsIterator{
public:
  DECL_ELEMENT_TYPE(Substitution);
  AllSubstitutionsIterator(Clause* cl,Instantiation* ins)
  {
    CALL("Instantiation::AllSubstitutionsIterator");
    DHMap<unsigned,TermList> sortedVars;
    SortHelper::collectVariableSorts(cl,sortedVars);
    VirtualIterator<std::pair<unsigned,TermList>> it = sortedVars.items();

    while(it.hasNext()){
       std::pair<unsigned,TermList> item = it.next();
       DArray<Term*>* array = new DArray<Term*>();
       array->initFromIterator(ins->getCandidateTerms(cl,item.first,item.second));
       candidates.insert(item.first,array);
       current.insert(item.first,0);
    }
    variables = candidates.domain();
    finished = !variables.hasNext();
    if(!finished) currently = variables.next();
  }

  bool hasNext(){ return !finished; }

  Substitution next()
  {
    CALL("AllSubstitutionsIterator::next")
    Substitution sub;
    VirtualIterator<unsigned> vs = candidates.domain(); 
    while(vs.hasNext()){
      unsigned v = vs.next();
      DArray<Term*>* cans;
      if(candidates.find(v,cans) && cans->size()!=0){
        unsigned at = current.get(v);
        sub.bind(v,(* cans)[at]);
      }
    }
    //cout << "sub is " << sub.toString() << endl;

    // now update points and set finished if we are
    if(!candidates.find(currently) || candidates.get(currently)->size()==0 || 
       candidates.get(currently)->size() == current.get(currently)+1){
      if(variables.hasNext()) currently = variables.next();
      else finished=true;
    }
    else{
      current.set(currently,(current.get(currently)+1));
    }

    return sub; 
  }

private:
  DHMap<unsigned,DArray<Term*>*> candidates;
  DHMap<unsigned,unsigned> current;
  VirtualIterator<unsigned> variables;
  unsigned currently;
  bool finished;
};

struct Instantiation::ResultFn
{
  ResultFn(Clause* cl) : _cl(cl) {}
  Clause* operator()(Substitution sub)
  {
    CALL("Instantiation::ResultFn::operator()");

    unsigned clen = _cl->length();
    Clause* res = new(clen) Clause(clen,GeneratingInference1(InferenceRule::INSTANTIATION,_cl));

    for(unsigned i=0;i<clen;i++){
      (*res)[i] = SubstHelper::apply((*_cl)[i],sub);
    }

    return res; 
  }
private:
  Clause* _cl;
};

ClauseIterator Instantiation::generateClauses(Clause* premise)
{
  CALL("Instantiation::generateClauses");

  //cout << "Instantiate " << premise->toString() << endl;

  Stack<Substitution> subs;
  for(unsigned i=0;i<premise->length();i++){
    Literal* lit = (*premise)[i];
    tryMakeLiteralFalse(lit,subs);
  }

  return pvi(getConcatenatedIterator(
  //return pvi(
               getMappingIterator(
                  getPersistentIterator(Stack<Substitution>::Iterator(subs)),
                  ResultFn(premise)
               ),
               getMappingIterator(
                 AllSubstitutionsIterator(premise,this),
                 ResultFn(premise)
              )
         ));

}

}