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
 * @file NegativeExt.cpp
 * Implements class NegativeExt.
 */

#if VHOL

#include <utility>

#include "Lib/VirtualIterator.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/PairUtils.hpp"

#include "Lib/Environment.hpp"
#include "Shell/Statistics.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/ApplicativeHelper.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/LiteralSelector.hpp"
#include "Saturation/SaturationAlgorithm.hpp"

#include "PositiveExt.hpp"

#if VDEBUG
#include <iostream>
using namespace std;
#endif

namespace Inferences
{

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

struct PositiveExt::IsPositiveEqualityFn
{
  bool operator()(Literal* l)
  { return l->isEquality() && l->isPositive(); }
};

struct PositiveExt::ResultFn
{
  ResultFn(Clause* cl) : _cl(cl), _cLen(cl->length()) {}
  
  Clause* operator() (Literal* lit) // f X = g X
  {
    CALL("PositiveExt::ResultFn::operator()");

    ASS(lit->isEquality());
    ASS(lit->isPositive());

    TermList lhs = *lit->nthArgument(0); //f X
    TermList rhs = *lit->nthArgument(1); //g X

    if(lhs.isApplication() && rhs.isApplication()){
      TermList left1 = lhs.lhs();  // f
      TermList right1 = lhs.rhs(); // X

      TermList left2 = rhs.lhs(); // g
      TermList right2 = rhs.rhs(); // X

      if(right1.isVar() && right2.isVar() && right1 == right2){
        unsigned var = right1.var(); // X
        // X doesn't occur in f and g
        if(!left1.isFreeVariable(var) && !left2.isFreeVariable(var)){
          bool occursInC = false;
          for(unsigned i=0;i<_cLen;i++) {
            Literal* curr=(*_cl)[i];
            if(curr!=lit && curr->isFreeVariable(var)) {
              occursInC = true;
            }
          }

          if(!occursInC){
            TermList sort = ApplicativeHelper::lhsSort(lhs);
            // f = g
            Literal* newLit = Literal::createEquality(true, left1, left2, sort);

            Clause* res = new(_cLen) Clause(_cLen, GeneratingInference1(InferenceRule::POSITIVE_EXT, _cl));

            for(unsigned i=0;i<_cLen;i++) {
              Literal* curr=(*_cl)[i];
              if(curr!=lit) {
                (*res)[i] = curr;
              } else {
                (*res)[i] = newLit;
              }
            }

            env.statistics->positiveExtensionality++;
         
            return res; // f = x \/ C'
          }
        }
      }
    }
    
    return 0;
  }
private:
  Clause* _cl; // f X = g X \/ C'
  unsigned _cLen;
};

ClauseIterator PositiveExt::generateClauses(Clause* premise)
{
  CALL("PositiveExt::generateClauses");

  if(premise->isEmpty()) {
    return ClauseIterator::getEmpty();
  }
  ASS(premise->numSelected()>0);

  auto it1 = premise->getSelectedLiteralIterator();

  auto it2 = getFilteredIterator(it1,IsPositiveEqualityFn());

  auto it3 = getMappingIterator(it2,ResultFn(premise));

  auto it4 = getFilteredIterator(it3,NonzeroFn());

  return pvi( it4 );
}

}

#endif
