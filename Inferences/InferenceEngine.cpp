
/*
 * File InferenceEngine.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file InferenceEngine.cpp
 * Implements class InferenceEngine amd its simple subclasses.
 */

#include "Lib/Environment.hpp"
#include "Lib/Random.hpp"
#include "Lib/DArray.hpp"
#include "Lib/List.hpp"
#include "Lib/Metaiterators.hpp"

#include "Kernel/Term.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/ApplicativeHelper.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Statistics.hpp"

#include "InferenceEngine.hpp"

#define DEBUG_DUPLICATE_LITERALS 0

namespace Inferences
{

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

typedef ApplicativeHelper AH;

/**
 * Return options that control the inference engine.
 *
 * This function may be called only when attached to the saturation algorithm,
 * unless a child class overrides this function.
 */
const Options& InferenceEngine::getOptions() const
{
  CALL("InferenceEngine::getOptions");
  ASS(attached());

  return _salg->getOptions();
}

CompositeISE::~CompositeISE()
{
  ISList::destroyWithDeletion(_inners);
}

/**
 * Add @c ise as the first simplification engine to be used
 *
 * This object takes ownership of the @c ise object and will be
 * responsible for its destruction.
 */
void CompositeISE::addFront(ImmediateSimplificationEngine* ise)
{
  ASS_EQ(_salg,0);
  ISList::push(ise,_inners);
}
void CompositeISE::addFrontMany(ImmediateSimplificationEngine* ise)
{
  ASS_EQ(_salg,0);
  ISList::push(ise,_innersMany);
}
ClauseIterator CompositeISE::simplifyMany(Clause* cl)
{
  ISList* curr=_innersMany;
  while(curr && cl) {
    ClauseIterator cIt=curr->head()->simplifyMany(cl);
    if(cIt.hasNext()){
      return cIt;
    } else {
      curr=curr->tail();      
    }
  }
  return ClauseIterator::getEmpty();
}
Clause* CompositeISE::simplify(Clause* cl)
{
  ISList* curr=_inners;
  while(curr && cl) {
    Clause* newCl=curr->head()->simplify(cl);
    if(newCl==cl) {
      curr=curr->tail();
    } else {
      return newCl;
    }
  }
  return cl;
}
void CompositeISE::attach(SaturationAlgorithm* salg)
{
  ImmediateSimplificationEngine::attach(salg);
  ISList::Iterator eit(_inners);
  while(eit.hasNext()) {
    eit.next()->attach(salg);
  }
}
void CompositeISE::detach()
{
  ISList::Iterator eit(_inners);
  while(eit.hasNext()) {
    eit.next()->detach();
  }
  ImmediateSimplificationEngine::detach();
}


//CompositeFSE::~CompositeFSE()
//{
//  _inners->destroy();
//}
//void CompositeFSE::addFront(ForwardSimplificationEngineSP fse)
//{
//  ASS_EQ(_salg,0);
//  FSList::push(fse,_inners);
//}
//void CompositeFSE::perform(Clause* cl, bool& keep, ClauseIterator& toAdd, ClauseIterator& premises)
//{
//  keep=true;
//  FSList* eit=_inners;
//  if(!eit) {
//    toAdd=ClauseIterator::getEmpty();
//    return;
//  }
//  while(eit && keep) {
//    eit->head()->perform(cl,keep,toAdd, premises);
//    eit=eit->tail();
//  }
//}
//void CompositeFSE::attach(SaturationAlgorithm* salg)
//{
//  ForwardSimplificationEngine::attach(salg);
//  FSList* eit=_inners;
//  while(eit) {
//    eit->head()->attach(salg);
//    eit=eit->tail();
//  }
//}
//void CompositeFSE::detach()
//{
//  FSList* eit=_inners;
//  while(eit) {
//    eit->head()->detach();
//    eit=eit->tail();
//  }
//  ForwardSimplificationEngine::detach();
//}

struct GeneratingFunctor
{
  DECL_RETURN_TYPE(ClauseIterator);

  GeneratingFunctor(Clause* cl) : cl(cl) {}
  OWN_RETURN_TYPE operator() (GeneratingInferenceEngine* gie)
  { return gie->generateClauses(cl); }
  Clause* cl;
};
CompositeGIE::~CompositeGIE()
{
  GIList::destroyWithDeletion(_inners);
}
void CompositeGIE::addFront(GeneratingInferenceEngine* fse)
{
  ASS_EQ(_salg,0);
  GIList::push(fse,_inners);
}
ClauseIterator CompositeGIE::generateClauses(Clause* premise)
{
  return pvi( getFlattenedIterator(
	  getMappingIterator(GIList::Iterator(_inners), GeneratingFunctor(premise))) );
}
void CompositeGIE::attach(SaturationAlgorithm* salg)
{
  GeneratingInferenceEngine::attach(salg);
  GIList* eit=_inners;
  while(eit) {
    eit->head()->attach(salg);
    eit=eit->tail();
  }
}
void CompositeGIE::detach()
{
  GIList* eit=_inners;
  while(eit) {
    eit->head()->detach();
    eit=eit->tail();
  }
  GeneratingInferenceEngine::detach();
}

Clause* ChoiceDefinitionISE::simplify(Clause* c)
{
  CALL("ChoiceDefinitionISE::simplify");

  if (c->length() != 2) {
    return c;
  }

  Literal* lit1 = (*c)[0];
  Literal* lit2 = (*c)[1];
  
  TermList x, f;

  if(!isPositive(lit1) && is_of_form_xy(lit1, x) &&
      isPositive(lit2) && is_of_form_xfx(lit2, x, f)){
    unsigned fun = f.term()->functor();
    env.signature->addChoiceOperator(fun);
    return 0;
  } else if(!isPositive(lit2) && is_of_form_xy(lit2, x) && 
             isPositive(lit1) && is_of_form_xfx(lit1, x, f)) {
    unsigned fun = f.term()->functor();
    env.signature->addChoiceOperator(fun);
    return 0;
  }
  return c;
}

bool ChoiceDefinitionISE::isPositive(Literal* lit) {
  CALL("ChoiceDefinitionISE::isPositive");

  TermList lhs = *lit->nthArgument(0);
  TermList rhs = *lit->nthArgument(1);
  if(!AH::isBool(lhs) && !AH::isBool(rhs)){ return false; }
  if(AH::isBool(lhs) && AH::isBool(rhs)){ return false; }
  if(AH::isBool(lhs)){ 
    return lit->polarity() == AH::isTrue(lhs);
  }
  if(AH::isBool(rhs)){ 
    return lit->polarity() == AH::isTrue(rhs);
  }
  return false;
};

bool ChoiceDefinitionISE::is_of_form_xy(Literal* lit, TermList& x){
  CALL("ChoiceDefinitionISE::is_of_form_xy");

  TermList term = AH::isBool(*lit->nthArgument(0)) ? *lit->nthArgument(1) : *lit->nthArgument(0);
  
  TermStack args;
  ApplicativeHelper::getHeadAndArgs(term, x, args);
  return (x.isVar() && args.size() == 1 && args[0].isVar());
}

bool ChoiceDefinitionISE::is_of_form_xfx(Literal* lit, TermList x, TermList& f){
  CALL("ChoiceDefinitionISE::is_of_form_xfx");
  
  TermList term = AH::isBool(*lit->nthArgument(0)) ? *lit->nthArgument(1) : *lit->nthArgument(0);
  
  TermStack args;
  TermList head;
  ApplicativeHelper::getHeadAndArgs(term, head, args);
  if(head == x && args.size() == 1){
    TermList arg = args[0];
    ApplicativeHelper::getHeadAndArgs(arg, f, args);
    return (!f.isVar() && args.size() == 1 && args[0] == x);
  }
  return false;
}

Clause* DuplicateLiteralRemovalISE::simplify(Clause* c)
{
  CALL("DuplicateLiteralRemovalISE::simplify");

  int length = c->length();
  if (length <= 1) {
    return c;
  }

  //literals that will be skipped, skipping starts on the top of the stack
  //and goes from the end of the clause
  static LiteralStack skipped;
  skipped.reset();

  //we handle low length specially, not to have to use the set
  if(length==2) {
    if((*c)[0]!=(*c)[1]) {
      return c;
    }
    skipped.push((*c)[0]);
  }
  else if(length==3) {
    if((*c)[0]!=(*c)[1]) {
      if((*c)[0]!=(*c)[2]) {
        if((*c)[1]!=(*c)[2]) {
          return c;
        }
      }
      skipped.push((*c)[2]);
    }
    else { //(*c)[0]==(*c)[1]
      skipped.push((*c)[0]);
      if((*c)[0]==(*c)[2]) {
        //all are equal
        skipped.push((*c)[0]);
      }
    }
  }
  else {
    static DHSet<Literal*> seen;
    seen.reset();
    //here we rely on the fact that the iterator traverses the clause from
    //the first to the last literal
    Clause::Iterator cit(*c);
    while(cit.hasNext()) {
      Literal* lit = cit.next();
      if(!seen.insert(lit)) {
        skipped.push(lit);
      }
    }
    if(skipped.isEmpty()) {
      return c;
    }
  }

  ASS(skipped.isNonEmpty());

  // there are duplicate literals, delete them from lits
  int newLength = length - skipped.length();
  // now lits[0 ... newLength-1] contain the remaining literals
  Clause* d = new(newLength)
		 Clause(newLength,
			c->inputType(),
			new Inference1(Inference::REMOVE_DUPLICATE_LITERALS,
				       c));

  int origIdx = length-1;

  for(int newIdx=newLength-1; newIdx>=0; newIdx--,origIdx--) {
    while(skipped.isNonEmpty() && (*c)[origIdx]==skipped.top()) {
      skipped.pop();
      origIdx--;
      ASS_GE(origIdx,0);
    }
    (*d)[newIdx] = (*c)[origIdx];
  }
  ASS(skipped.isEmpty());
  ASS_EQ(origIdx,-1);
  d->setAge(c->age());
  env.statistics->duplicateLiterals += length - newLength;

#if DEBUG_DUPLICATE_LITERALS
  {
    static DHSet<Literal*> origLits;
    origLits.reset();
    static DHSet<Literal*> newLits;
    newLits.reset();
    origLits.loadFromIterator(Clause::Iterator(*c));
    newLits.loadFromIterator(Clause::Iterator(*d));
    ASS_EQ(origLits.size(),newLits.size());
    ASS_EQ(origLits.size(), static_cast<unsigned>(newLength));
  }
#endif

  return d;
}

Clause* TautologyDeletionISE2::simplify(Clause* c)
{
  CALL("TautologyDeletionISE2::simplify");

  typedef ApplicativeHelper AH;

  static LiteralStack negLits;
  static LiteralStack posLits;

  negLits.reset();
  posLits.reset();

  for(unsigned i = 0; i < c->length(); i++){
    Literal* lit = (*c)[i];
    TermList lhs = *lit->nthArgument(0);
    TermList rhs = *lit->nthArgument(1);
    if(!lit->polarity() && AH::isBool(lhs) && AH::isBool(rhs) &&
      (AH::isTrue(lhs) != AH::isTrue(rhs))){
      //false != true
      return 0;
    }

    if(AH::isBool(lhs)){
      AH::isTrue(lhs) == lit->polarity() ? posLits.push(lit) : negLits.push(lit); 
    } else if (AH::isBool(rhs)){
      AH::isTrue(rhs) == lit->polarity() ? posLits.push(lit) : negLits.push(lit);   
    }
  }

  for(unsigned i =0; i < posLits.size(); i++){
    Literal* posLit = posLits[i];
    TermList posNonBooleanSide = *posLit->nthArgument(0);
    if(AH::isBool(posNonBooleanSide)){
      posNonBooleanSide = *posLit->nthArgument(1);
    }
    ASS(!AH::isBool(posNonBooleanSide));
    for(unsigned j = 0; j < negLits.size(); j++){
      Literal* negLit = negLits[j];
      TermList negNonBooleanSide = *negLit->nthArgument(0);
      if(AH::isBool(negNonBooleanSide)){
        negNonBooleanSide = *negLit->nthArgument(1);
      }
      ASS(!AH::isBool(negNonBooleanSide));
      if(posNonBooleanSide == negNonBooleanSide){
        //t = true \/ t = false
        //t = true \/ t != true
        return 0;
      }
    }
  }

  return c;
}

Clause* TrivialInequalitiesRemovalISE::simplify(Clause* c)
{
  CALL("TrivialInequalitiesRemovalISE::simplify");

  static DArray<Literal*> lits(32);

  int length = c->length();
  int j = 0;
  lits.ensure(length);
  int found = 0;
  for (int i = length-1;i >= 0;i--) {
    Literal* l = (*c)[i];
    if (!l->isEquality()) {
      lits[j++] = l;
      continue;
    }
    TermList* t1 = l->args();
    TermList* t2 = t1->next();
    if((isTrue(*t1) && isFalse(*t2) && l->polarity()) || 
       (isTrue(*t2) && isFalse(*t1) && l->polarity())){
      found++;
      continue;
    }
    if(l->isPositive()){
      lits[j++] = l;
      continue;
    }
    if (t1->sameContent(t2)) {
      found++;
    }
    else {
      lits[j++] = l;
    }
  }

  if (found == 0) {
    return c;
  }

  int newLength = length - found;
  Clause* d = new(newLength)
                Clause(newLength,
		       c->inputType(),
		       new Inference1(Inference::TRIVIAL_INEQUALITY_REMOVAL,
				      c));
  for (int i = newLength-1;i >= 0;i--) {
    (*d)[i] = lits[newLength-i-1];
  }
  d->setAge(c->age());
  env.statistics->trivialInequalities += found;

  return d;
}

}
