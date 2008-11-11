/**
 * @file Forwards.hpp
 * Forward declarations of (some) classes in Kernel namespace
 */

#ifndef __Kernel_Forwards__
#define __Kernel_Forwards__

#include "../Lib/Forwards.hpp"


namespace Kernel
{

using namespace Lib;

class TermList;
class Term;
class Literal;
class Clause;

typedef VirtualIterator<Clause*> ClauseIterator;

};


#endif /* __Kernel_Forwards__ */
