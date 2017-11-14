
/*
 * File Selector.hpp.
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
 * @file Selector.hpp
 * Defines class Selector.
 */

#ifndef __Selector__
#define __Selector__

#include "Forwards.hpp"

#include "Shell/SineUtils.hpp"
#include "Lib/VString.hpp"

#include "Storage.hpp"

namespace Shell
{
namespace LTB
{

using namespace std;
using namespace Kernel;

class Selector
{
public:
  Selector() : _storage(true) {}
  StringList* theoryFileNames()
  { return _storage.getTheoryFileNames(); }

  void selectForProblem(UnitList*& units);
private:
  Storage _storage;
};

}
}

#endif // __Selector__
