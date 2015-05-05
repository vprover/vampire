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

#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Sorts.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Substitution.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Theory.hpp"

#include "Shell/Statistics.hpp"

#include "Instantiation.hpp"

namespace Inferences
{

using namespace Lib;
using namespace Kernel;

struct IntToTermFn
{
  IntToTermFn(){}
  DECL_RETURN_TYPE(Term*);
  OWN_RETURN_TYPE operator()(unsigned int i)
  {
    return theory->representConstant(IntegerConstantType(i));
  }
};

VirtualIterator<Term*> Instantiation::getCandidateTerms(Clause* cl, unsigned var,unsigned sort)
{
  CALL("Instantiation::getCandidateTerms");

  if(sort==Sorts::SRT_INTEGER){
    return pvi(getMappingIterator(getRangeIterator(0u,10u),IntToTermFn()));
  }

  return VirtualIterator<Term*>::getEmpty(); 
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
      // check deals with case where there are no candidates and no binding
      if(cans->size()!=0) sub.bind(v,(* cans)[at]);
    }
    cout << "sub is " << sub.toString() << endl;

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

  return pvi(getMappingIterator(
               AllSubstitutionsIterator(premise,this),
               ResultFn(premise)
         ));
}

}
