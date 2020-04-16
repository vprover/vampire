
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
			new Inference1(Inference::Rule::REMOVE_DUPLICATE_LITERALS,c));

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
    if (l->isPositive() || ! l->isEquality()) {
      lits[j++] = l;
      continue;
    }
    TermList* t1 = l->args();
    TermList* t2 = t1->next();
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
		       new Inference1(Inference::Rule::TRIVIAL_INEQUALITY_REMOVAL,c));
  for (int i = newLength-1;i >= 0;i--) {
    (*d)[i] = lits[newLength-i-1];
  }
  d->setAge(c->age());
  env.statistics->trivialInequalities += found;

  return d;
}

}
