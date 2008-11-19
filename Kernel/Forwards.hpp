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
typedef SingleParamEvent<Clause*> ClauseEvent;

class DoubleSubstitution;
typedef SmartPtr<DoubleSubstitution> DoubleSubstitutionSP;
typedef SmartPtr<const DoubleSubstitution> DoubleSubstitutionCSP;


};


#endif /* __Kernel_Forwards__ */
