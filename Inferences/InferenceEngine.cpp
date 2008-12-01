/**
 * @file InferenceEngine.cpp
 * Implements class InferenceEngine amd its simple subclasses.
 */

#include "../Lib/Environment.hpp"
#include "../Lib/Random.hpp"
#include "../Lib/DArray.hpp"
#include "../Lib/List.hpp"
#include "../Kernel/Term.hpp"
#include "../Kernel/Clause.hpp"
#include "../Kernel/Inference.hpp"
#include "../Shell/Statistics.hpp"
#include "InferenceEngine.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;
using namespace Inferences;


CompositeFSE::~CompositeFSE()
{
  _inners->destroy();
}
void CompositeFSE::addFront(ForwardSimplificationEngine* fse)
{
  FSList::push(fse,_inners);
}
void CompositeFSE::perform(Clause* cl, bool& keep, ClauseIterator& toAdd)
{
  keep=true;
  FSList* eit=_inners;
  if(!eit) {
    toAdd=ClauseIterator::getEmpty();
    return;
  }
  while(eit && keep) {
    eit->head()->perform(cl,keep,toAdd);
    eit=eit->tail();
  }
}
void CompositeFSE::attach(SaturationAlgorithm* salg)
{
  ForwardSimplificationEngine::attach(salg);
  FSList* eit=_inners;
  while(eit) {
    eit->head()->attach(salg);
    eit=eit->tail();
  }
}
void CompositeFSE::detach()
{
  FSList* eit=_inners;
  while(eit) {
    eit->head()->detach();
    eit=eit->tail();
  }
  ForwardSimplificationEngine::detach();
}


struct GeneratingFunctor
{
  GeneratingFunctor(Clause* cl) : cl(cl) {}
  ClauseIterator operator() (GeneratingInferenceEngine* gie)
  { return gie->generateClauses(cl); }
  Clause* cl;
};
CompositeGIE::~CompositeGIE()
{
  _inners->destroy();
}
void CompositeGIE::addFront(GeneratingInferenceEngine* fse)
{
  GIList::push(fse,_inners);
}
ClauseIterator CompositeGIE::generateClauses(Clause* premise)
{
  VirtualIterator<ClauseIterator> iterators =
    getMappingIterator<ClauseIterator>(GIList::Iterator(_inners), GeneratingFunctor(premise));
  return getFlattenedIterator(iterators);
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


void DuplicateLiteralRemovalFSE::perform(Clause* c, bool& keep, ClauseIterator& toAdd)
{
  CALL("DuplicateLiteralRemovalFSE::perform");

  int length = c->length();
  if (length <= 1) {
    keep=true;
    toAdd=ClauseIterator::getEmpty();
    return;
  }

  // array behaves as a stack of calls to quicksort
  static DArray<int> ft(32);
  static DArray<Literal*> lits(32); // literals to sort
  ft.ensure(length);
  lits.ensure(length);

  int p = 0; // pointer to the next element in ft
  for (int i = length-1;i >= 0;i--) {
    lits[i] = (*c)[i];
  }

  // sorting will be between from and to
  int from = 0;
  int to = length-1;
  int found = 0;
  for (;;) {
    // invariant: from < to
    int m = from + Random::getInteger(to-from+1);
    Literal* mid = lits[m];
    int l = from;
    int r = to;
    while (l < m) {
      if ((void*)lits[l] < (void*)mid) {
	l++;
      }
      else if ((void*)lits[l] == (void*)mid) {
	found++;
	lits[l] = lits[from];
	lits[from] = 0;
	from++;
	l++;
      }
      else if (m == r) {
	lits[m] = lits[l];
	lits[l] = lits[m-1];
	lits[m-1] = mid;
	m--;
	r--;
      }
      else {
	ASS(m < r);
	Literal* lit = lits[l];
	lits[l] = lits[r];
	lits[r] = lit;
	r--;
      }
    }
    // l == m
    // now literals in lits[from ... m-1] are smaller than lits[m]
    // and literals in lits[r+1 ... to] are greater than lits[m]
    while (m < r) {
      if ((void*)mid < (void*)lits[m+1]) {
	Literal* lit = lits[r];
	lits[r] = lits[m+1];
	lits[m+1] = lit;
	r--;
      }
      else if ((void*)mid == (void*)lits[m+1]) {
	found++;
	lits[m+1] = lits[r];
	lits[r] = lits[to];
	lits[to] = 0;
	to--;
	r--;
      }
      else {
	lits[m] = lits[m+1];
	lits[m+1] = mid;
	m++;
      }
    }
    // now literals in lits[from ... m-1] are smaller than lits[m]
    // and all literals in lits[m+1 ... to] are greater than lits[m]
    if (m+1 < to) {
      ft[p++] = m+1;
      ft[p++] = to;
    }

    to = m-1;
    if (from < to) {
      continue;
    }

    if (p != 0) {
      p -= 2;
      ASS(p >= 0);
      from = ft[p];
      to = ft[p+1];
      continue;
    }

    // the stack is empty, finished
    if (found == 0) {
      keep=true;
      toAdd=ClauseIterator::getEmpty();
      return;
    }
    // there are duplicate literals, delete them from lits
    int newLength = length - found;
    // now lits[0 ... newLength-1] contain the remaining literals
    env.statistics->duplicateLiterals += found;
    Clause* d = new(newLength)
                   Clause(newLength,
			  c->inputType(),
			  new Inference1(Inference::REMOVE_DUPLICATE_LITERALS,
					 c));
    int next = 0;
    for (int f = length-1;f >= 0;f--) {
      if (lits[f]) {
	(*d)[next++] = lits[f];
      }
    }
    ASS(next == newLength);
    d->setAge(c->age());
    d->computeWeight();

    keep=false;
    toAdd=getSingletonIterator(d);
    return;
  }
}


void TrivialInequalitiesRemovalFSE::perform(Clause* c, bool& keep, ClauseIterator& toAdd)
{
  CALL("TrivialInequalitiesRemovalFSE::perform");

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
    keep=true;
    toAdd=ClauseIterator::getEmpty();
    return;
  }

  env.statistics->trivialInequalities += found;
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
  d->computeWeight();

  keep=false;
  toAdd=getSingletonIterator(d);
  return;
}

