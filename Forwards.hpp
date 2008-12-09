/**
 * @file Forwards.hpp
 * Forward declarations of some classes
 */

#ifndef __Forwards__
#define __Forwards__

namespace Lib
{
template<typename T> class VirtualIterator;
template<typename T> class SmartPtr;
template<typename T> class SingleParamEvent;
template<class C> class DArray;
template<class C> class Stack;
template<typename T> class List;
template <typename T, class Comparator> class BinaryHeap;

class BacktrackData;
};

namespace Kernel
{
using namespace Lib;

class Signature;

class TermList;
class Term;
class Literal;
typedef List<Literal*> LiteralList;

class Unit;
class Clause;
typedef VirtualIterator<Clause*> ClauseIterator;
typedef SingleParamEvent<Clause*> ClauseEvent;
typedef List<Clause*> ClauseList;

class DoubleSubstitution;
class Renaming;

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
