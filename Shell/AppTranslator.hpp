
/*
 * File AppTranslator.hpp.
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
 * @file AppTranslator.hpp
 */

#ifndef __AppTranslator__
#define __AppTranslator__

#include "Forwards.hpp"

#include "Kernel/Unit.hpp"

namespace Shell {

using namespace Kernel;

/**
 */
class AppTranslator
{
public:
  static Clause* translate (Clause*);
  static Literal* translate (Literal*);
  static TermList translate (TermList);
  static Term* translate (Term*);

private:
}; // class AppTranslator

}

#endif
