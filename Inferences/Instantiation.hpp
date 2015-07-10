/**
 * @file Instantiation.hpp
 * Defines class Instantiation
 * @author Giles
 */

#ifndef __Instantiation__
#define __Instantiation__

#include "Forwards.hpp"
#include "Lib/Set.hpp"
#include "Kernel/Sorts.hpp"

#include "InferenceEngine.hpp"

namespace Inferences
{

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
*/
class Instantiation
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(Instantiation);
  USE_ALLOCATOR(Instantiation);

  Instantiation() {}

  ClauseIterator generateClauses(Clause* premise);

  void registerClause(Clause* cl);

private:
  //bool getRelevantTerms(Clause* cl,unsigned sort, Set<Term*>* candidates);
  //VirtualIterator<Term*> getCandidateTerms(Clause* cl, unsigned var,unsigned sort);
  //class AllSubstitutionsIterator;
  struct ResultFn;

  bool tryMakeLiteralFalse(Literal*, Substitution& sub);
  Term* tryGetDifferentValue(Term* t); 

  DHMap<unsigned,Lib::Set<Term*>*> sorted_candidates;

};

};

#endif /*__Instantiation__*/
