/**
 * @file Selector.hpp
 * Defines class Selector.
 */

#ifndef __Selector__
#define __Selector__

#include <string>

#include "Forwards.hpp"

#include "Shell/SineUtils.hpp"

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
