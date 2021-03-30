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
 * @file ArrayTheoryISE.hpp
 * Defines class ArrayTheoryISE.
 *
 * The "extensionality resolution project" initially started out to improve
 * Vampire's reasoning in the theory of arrays. A first attempt was to add some
 * simple rewrite rules. However, the code here is not used at the moment.
 *
 * Adding this rewrite rules might be useful, but then the code has to be
 * revised. For example, applying rewrite rules exhaustively is implemented very
 * inefficiently.
 */

#ifndef __ArrayTheoryISE__
#define __ArrayTheoryISE__

#include "Forwards.hpp"
#include "Inferences/InferenceEngine.hpp"
#include "Kernel/TermTransformer.hpp"

namespace Inferences {

class ArrayTermTransformer
  :  public TermTransformer
{
public:
  ArrayTermTransformer();
  ~ArrayTermTransformer();
  Literal* rewriteNegEqByExtensionality(Literal* l);
protected:
  TermList transformSubterm(TermList trm);
};

class ArrayTheoryISE
  : public ImmediateSimplificationEngine
{
public:
  CLASS_NAME(ArrayTheoryISE);
  USE_ALLOCATOR(ArrayTheoryISE);

  ArrayTheoryISE();
  Clause* simplify(Clause* cl);
private:
  ArrayTermTransformer _transformer;
};

};

#endif /* __ArrayTheoryISE__ */
