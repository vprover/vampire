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
 * @file TermSubstitutionTree.cpp
 * Implements class TermSubstitutionTree.
 */

#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/ApplicativeHelper.hpp"
#include "TermSubstitutionTree.hpp"

#if VHOL
#include "Indexing/HOLSubstitutionTree.hpp"
#endif

namespace Indexing
{

using namespace Lib;
using namespace Kernel;


TermSubstitutionTree::TermSubstitutionTree(SplittingAlgo algo)
#if VHOL
  : _extra(false), _algo(algo) 
#endif
{ 
  switch(algo){
    case SplittingAlgo::NONE:
      _tree.reset(new SubstitutionTree());
      break;
#if VHOL
    case SplittingAlgo::HOL_UNIF:
      _tree.reset(new SubstitutionTree());
      break;
    case SplittingAlgo::HOL_MATCH:
      _tree.reset(new HOLSubstitutionTree([](TermList t){     
          return !t.isLambdaTerm();
        } ));
      break;      
#endif
  }

}

} // namespace  Indexing
