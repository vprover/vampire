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
 * @file CombinatorDemodISE.hpp
 * Defines class CombinatorDemodISE.
 */


#ifndef __CombinatorDemodISE__
#define __CombinatorDemodISE__

#include "Forwards.hpp"
#include "InferenceEngine.hpp"
#include "Kernel/TermTransformer.hpp"

namespace Inferences {

class TermReducer : public TermTransformer {
public:
  TermReducer() : TermTransformer(false, true), _reducLen(0) {} 
  TermList transformSubterm(TermList trm) override;
  
  // TODO are we calculating reduction length in the best way?
  // should we not be counting individual reductions rahter than the number
  // of separate head normal forms achieved?
  unsigned getReductionLen(){ return _reducLen; }
 
private:
  unsigned _reducLen;
};


class CombinatorDemodISE
: public ImmediateSimplificationEngine
{
public:
  CLASS_NAME(CombinatorDemodISE);
  USE_ALLOCATOR(CombinatorDemodISE);

  static TermList headNormalForm(TermList t);

  CombinatorDemodISE(){}
  Clause* simplify(Clause* cl);
};

};

#endif /* __CombinatorDemodISE__ */
