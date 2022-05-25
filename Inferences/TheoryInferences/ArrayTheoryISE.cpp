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
 * @file ArrayTheoryISE.cpp
 * Implements class ArrayTheoryISE.
 *
 * NOTE: This code is unfinished and not in use at the moment. See the comment
 * in the header file.
 */

#include "Inferences/ArrayTheoryISE.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Theory.hpp"
#include "Lib/DArray.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Random.hpp"
#include "Shell/Skolem.hpp"
#include "Shell/Statistics.hpp"

namespace Inferences
{

using namespace Lib;
using namespace Kernel;
using namespace Inferences;

ArrayTermTransformer::ArrayTermTransformer() {}

ArrayTermTransformer::~ArrayTermTransformer() {}

TermList ArrayTermTransformer::transformSubterm(TermList trm)
{
  CALL("ArrayTermTransformer::transformSubterm");
  
  if (!trm.isTerm()) {
    return trm;
  }
  
  Term* term = trm.term();
  Interpretation interp = theory->interpretFunction(term->functor());
  if(!theory->isArrayOperation(interp)) return trm;

  switch(theory->convertToStructured(interp){

  case StructuredStoreInterpretation::ARRAY_SELECT :
    TermList* array = term->nthArgument(0);
    
    if (array->isTerm() &&
        (array->term()->functor() == _store1Functor ||
         array->term()->functor() == _store2Functor))
    {
      // r(w(A,I,V),I) => V
      Term* store = term->nthArgument(0)->term();
      
      TermList* selectIndex = term->nthArgument(1);
      TermList* storeIndex = store->nthArgument(1);
      
      if (selectIndex->sameContent(storeIndex)) {
        return *store->nthArgument(2);
      }
      break;
  case StructuredStoreInterpretation::ARRAY_STORE:
    TermList* array = term->nthArgument(0);
    TermList* value = term->nthArgument(2);
    
    if (array->isTerm()){

      Interpretation arrayInterp = theory->getInterpretation(array->term()->functor());
      if(!(theory->isArrayOperation(arrayInterp) &&
           theory->convertToStructured(arrayInterp)==StructuredSortInterpretation::ARRAY_STORE))
      { break;}

      // w(w(A,I,V1),I,V2) => w(A,I,V2)
      Term* store = array->term();
      TermList* outerIndex = term->nthArgument(1);
      TermList* innerIndex = store->nthArgument(1);
      
      if (outerIndex->sameContent(innerIndex)) {
        TermList args[3];
        args[0] = *store->nthArgument(0);
        args[1] = *outerIndex;
        args[2] = *value;
        return TermList(Term::create(term, args));
      }
    } else if (value->isTerm()){ 

      Interpretation valueInterp = theory->getInterpretation(value->term()->functor());
      if(!(theory->isArrayOperation(valueInterp) &&
           theory->convertToStructured(valueInterp)==StructuredSortInterpretation::ARRAY_SELECT))
      { break;}

      // w(A,I,r(A,I)) => A
      TermList* selectArray = value->term()->nthArgument(0);
      TermList* selectIndex = value->term()->nthArgument(1);
      TermList* storeIndex = term->nthArgument(1);
      
      if (selectArray->sameContent(array) &&
          selectIndex->sameContent(storeIndex)) {
        return *array;
      }
    }
    break;

  default: ASSERTION_VIOLATION;

  }
  
  return trm;
}

Literal* ArrayTermTransformer::rewriteNegEqByExtensionality(Literal* l)
{
  CALL("ArrayTermTransformer::rewriteNegEqByExtensionality");
  
  if (l->isEquality() && l->isNegative()) {
    unsigned sort = SortHelper::getEqualityArgumentSort(l);
    unsigned select = theory->getSymbolForStructuredSort(sort, Theory::StructuredSortInterpretation::ARRAY_SELECT);
    unsigned valSort = theory->getArrayOperationSort(theory->interpretFunction(select));

    //cout << l->toString() << endl;
    TermList* lhs = l->nthArgument(0);
    TermList* rhs = l->nthArgument(1);
    
    // unsigned skolemFunction = Skolem::addSkolemFunction(0, 0, Sorts::SRT_INTEGER, "adiff");
    // TermList skolemTerm(Term::create(skolemFunction, 0, 0));
    TermList params[] = {*lhs, *rhs};
    unsigned sk = theory->getArrayExtSkolemFunction(sort);
    TermList skolemTerm(Term::create(sk, 2, params));
    
    TermList sel1(Term::create2(select, *lhs, skolemTerm));
    TermList sel2(Term::create2(select, *rhs, skolemTerm));
    
    return Literal::createEquality(false, sel1, sel2, valSort);
  }
  
  return l;
}

ArrayTheoryISE::ArrayTheoryISE() :
  _transformer(ArrayTermTransformer()) {}

Clause* ArrayTheoryISE::simplify(Clause* c)
{
  CALL("ArrayTheoryISE::simplify");
  
  if (c->inputType() == Unit::AXIOM) {
    return c;
  }
  
  static DArray<Literal*> lits(32);
  int length = c->length();
  lits.ensure(length);
  bool modified = false;
  
  // BK: is there a (performance, ...) reason for the decreasing counter?
  //for (int i = length-1; i >= 0;i--) {
  for (int i = 0; i < length; ++i) {
    Literal* l = (*c)[i];
    bool done = false;
    Literal* transformed;
    
    // BK: is there already a "deep" simplifier? i.e. one that performs
    // recursive simplification also on the arguments of already simplified
    // terms.
    while (!done) {
      //cout << "before: " << l->toString() << endl;
      transformed = _transformer.transform(l);
      //cout << "after:  " << transformed->toString() << endl;
      
      if (l != transformed) {
        modified = true;
        l = transformed;
      } else {
        done = true;
      }
    }
    
    Literal* transformed2 = _transformer.rewriteNegEqByExtensionality(transformed);
    if (transformed2 != transformed) {
      modified = true;
    }
    
    lits[i] = transformed2;
  }
  
  if (modified) {
    // BK: inference rule?
    Clause* d = new(length)
      Clause(length,
             c->inputType(),
             new Inference1(Inference::INTERPRETED_SIMPLIFICATION, c));
    for (int i = 0; i < length; ++i) {
      (*d)[i] = lits[i];
    }
    d->setAge(c->age());
    // BK: should we keep some statistics?
    //cout << "before: " << c->toString() << endl;
    //cout << "after:  " << d->toString() << endl;
    return d;
  }
  
  return c;
}

}
