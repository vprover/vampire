/**
 * @file Forwards.hpp
 * Forward declarations of some classes
 */

#ifndef __Forwards__
#define __Forwards__

//TODO: Remove for non-debugging builds.
#ifndef VDEBUG
#define VDEBUG
#endif

namespace Lib 
{

template<typename T>
class VirtualIterator;
template<typename T>
class SmartPtr;
template<typename T>
class SingleParamEvent;
template<class C>
class Stack;
template<typename T>
class List;
template <typename T, class Comparator>
class BinaryHeap;
class BacktrackData;
};

namespace Kernel
{
using namespace Lib;

class TermList;
class Term;
class Literal;

class Unit;
class Clause;
typedef VirtualIterator<Clause*> ClauseIterator;
typedef SingleParamEvent<Clause*> ClauseEvent;

class DoubleSubstitution;
typedef SmartPtr<DoubleSubstitution> DoubleSubstitutionSP;
typedef SmartPtr<const DoubleSubstitution> DoubleSubstitutionCSP;

class LiteralSelector;
};

namespace Indexing
{
class Index;
class IndexManager;
};

namespace Saturation 
{
class SaturationAlgorithm;
class ClauseContainer;
class UnprocessedClauseContainer;
class PassiveClauseContainer;
class ActiveClauseContainer;
}

#endif /* __Forwards__ */
