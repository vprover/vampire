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
bool Instantiation::tryMakeLiteralFalse(Literal* lit, Substitution& sub)
{
  CALL("Instantiation::tryMakeLiteralFalse");

    bool madeSub = false;
    if(theory->isInterpretedPredicate(lit)){ 
      Interpretation interpretation = theory->interpretPredicate(lit);
      //unsigned sort = theory->getOperationSort(interpretation);

      //TODO, very limited consideration, expand
      switch(interpretation){
        case Theory::EQUAL:
        {
          TermList* left = lit->nthArgument(0); TermList* right = lit->nthArgument(1); 
          unsigned var;
          Term* t = 0;
          if(left->isVar() && !right->isVar() && theory->isInterpretedConstant(right->term())){
           t = right->term(); 
           var = left->var();
          }
          if(right->isVar() && !left->isVar() && theory->isInterpretedConstant(left->term())){
           t = left->term(); 
           var = right->var();
          }
          if(t){
            madeSub = true;
            if(lit->polarity()){
             t = tryGetDifferentValue(t);
            }
            if(t){
              sub.bind(var,t);
            }
          }
          break;
        }
        default: //TODO cover other cases
          break;
      }
    }

    return madeSub;
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

/*
VirtualIterator<Term*> Instantiation::getCandidateTerms(Clause* cl, unsigned var,unsigned sort)
{
  CALL("Instantiation::getCandidateTerms");

  Set<Term*>* cans=0;
  VirtualIterator<Term*> res = VirtualIterator<Term*>::getEmpty();
  if(sorted_candidates.find(sort,cans)){
    res = pvi(Set<Term*>::Iterator(*cans));
  }

  Set<Term*>* relCans = new Set<Term*>();
  if(getRelevantTerms(cl,sort,relCans)){
    res = pvi(getConcatenatedIterator(res,Set<Term*>::Iterator(*relCans))); 
  }

  return pvi(res);
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
*/

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

  cout << "Instantiate " << premise->toString() << endl;

  Stack<Substitution> subs;
  for(unsigned i=0;i<premise->length();i++){
    Literal* lit = (*premise)[i];
    Substitution sub;
    if(tryMakeLiteralFalse(lit,sub)){ 
      //cout << "pushing " << sub.toString() << endl;
      subs.push(sub);
    }
  }

  return pvi(getMappingIterator(
                getPersistentIterator(Stack<Substitution>::Iterator(subs)),
                ResultFn(premise)
         ));

/*
  return pvi(getMappingIterator(
               AllSubstitutionsIterator(premise,this),
               ResultFn(premise)
         ));
*/
}

}
