/**
 * @file Selector.hpp
 * Defines class Selector.
 */

#ifndef __Selector__
#define __Selector__

#include <string>

#include "Forwards.hpp"

namespace Shell
{
namespace LTB
{

using namespace std;
using namespace Kernel;

class Selector
{
public:
  ClauseList* selectForProblem(string fname);
};

}
}

#endif // __Selector__
