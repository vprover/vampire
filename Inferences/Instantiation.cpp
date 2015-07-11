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
#include "Kernel/Sorts.hpp"
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
  DECL_RETURN_TYPE(Term*);
  OWN_RETURN_TYPE operator()(unsigned int i)
  {
    return theory->representConstant(IntegerConstantType(i));
  }
};
struct IntToRatTermFn
{
  IntToRatTermFn(){}
  DECL_RETURN_TYPE(Term*);
  OWN_RETURN_TYPE operator()(unsigned int i)
  {
    return theory->representConstant(RationalConstantType(i,1));
  }
};
struct IntToRealTermFn
{
  IntToRealTermFn(){}
  DECL_RETURN_TYPE(Term*);
  OWN_RETURN_TYPE operator()(unsigned int i)
  {
    return theory->representConstant(RealConstantType(RationalConstantType(i,1)));
  }
};

struct InvertNumber
{
  InvertNumber();
  DECL_RETURN_TYPE(unsigned);
  OWN_RETURN_TYPE operator()(unsigned int i){ return -i; }
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
        unsigned sort;
        if(SortHelper::tryGetResultSort(t,sort)){
          if(sort==Sorts::SRT_DEFAULT) continue;
          Set<Term*>* cans;
          if(sorted_candidates.isEmpty() || !sorted_candidates.find(sort,cans)){
            cans = new Set<Term*>();
            sorted_candidates.insert(sort,cans);
          }
          // cout << "For sort " << sort << " there are " << cans->size() << " cans" <<endl;
          cans->insert(t.term());
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

    if(theory->isInterpretedPredicate(lit)){ 
      Interpretation interpretation = theory->interpretPredicate(lit);
      //unsigned sort = theory->getOperationSort(interpretation);

      //TODO, very limited consideration, expand
      switch(interpretation){
        case Theory::EQUAL:
        case Theory::INT_LESS_EQUAL: // do these less_equal cases make sense?
        case Theory::RAT_LESS_EQUAL:
        case Theory::REAL_LESS_EQUAL:
        {
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
          break;
        }
        default: //TODO cover other cases
          break;
      }
    }

}

Term* Instantiation::tryGetDifferentValue(Term* t)
{
  CALL("Instantiation::tryGetDifferentValue");

  unsigned sort = SortHelper::getResultSort(t);

        switch(sort){
          case Sorts::SRT_INTEGER:
            {
              IntegerConstantType constant;
              ALWAYS(theory->tryInterpretConstant(t,constant));
              return theory->representConstant(constant+1);
            }
          case Sorts::SRT_RATIONAL:
            {
              RationalConstantType constant;
              RationalConstantType one(1,1);
              ALWAYS(theory->tryInterpretConstant(t,constant));
              return theory->representConstant(constant+one);
            }
          case Sorts::SRT_REAL:
            {
              RealConstantType constant;
              RealConstantType one(RationalConstantType(1,1));
              ALWAYS(theory->tryInterpretConstant(t,constant));
              return theory->representConstant(constant+one);
            }
          default:
            ASSERTION_VIOLATION;
        }

  return 0;
}

VirtualIterator<Term*> Instantiation::getCandidateTerms(Clause* cl, unsigned var,unsigned sort)
{
  CALL("Instantiation::getCandidateTerms");

  Set<Term*>* cans=0;
  VirtualIterator<Term*> res = VirtualIterator<Term*>::getEmpty();
  if(sorted_candidates.find(sort,cans)){
    res = pvi(Set<Term*>::Iterator(*cans));
  }
  return res; 
}

class Instantiation::AllSubstitutionsIterator{
public:
  AllSubstitutionsIterator(Clause* cl,Instantiation* ins)
  {
    CALL("Instantiation::AllSubstitutionsIterator");
    DHMap<unsigned,unsigned> sortedVars;
    SortHelper::collectVariableSorts(cl,sortedVars);
    VirtualIterator<std::pair<unsigned,unsigned>> it = sortedVars.items();

    while(it.hasNext()){
       std::pair<unsigned,unsigned> item = it.next();
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
    Substitution sub;
    VirtualIterator<unsigned> vs = candidates.domain(); 
    while(vs.hasNext()){
      unsigned v = vs.next();
      unsigned at = current.get(v);
      DArray<Term*>* cans = candidates.get(v);
      ASS(cans);
      // check deals with case where there are no candidates and no binding
      if(cans->size()!=0){
        sub.bind(v,(* cans)[at]);
      }
    }
    //cout << "sub is " << sub.toString() << endl;

    // now update points and set finished if we are
    if(candidates.get(currently)->size()==0 || 
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
  DECL_RETURN_TYPE(Clause*);
  OWN_RETURN_TYPE operator()(Substitution sub)
  {
    CALL("Instantiation::ResultFn::operator()");

    Inference* inf = new Inference1(Inference::INSTANTIATION,_cl);
    unsigned clen = _cl->length();
    Clause* res = new(clen) Clause(clen,_cl->inputType(),inf);
    res->setAge(_cl->age()+1);

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
