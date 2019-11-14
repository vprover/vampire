
/*
 * File CombinatorDemodISE.hpp.
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
 * @file CombinatorDemodISE.hpp
 * Defines class CombinatorDemodISE.
 */


#ifndef __CombinatorDemodISE__
#define __CombinatorDemodISE__

#include "Forwards.hpp"
#include "InferenceEngine.hpp"

namespace Inferences {

class CombinatorDemodISE
: public ImmediateSimplificationEngine
{
public:
  CLASS_NAME(CombinatorDemodISE);
  USE_ALLOCATOR(CombinatorDemodISE);

  CombinatorDemodISE(){}
  Clause* simplify(Clause* cl);
private:
   TermList reduce(TermList t);
   bool headNormalForm(TermList& t);
};

};

#endif /* __CombinatorDemodISE__ */
