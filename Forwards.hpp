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
class Substitution;

class LiteralSelector;
typedef Lib::SmartPtr<LiteralSelector> LiteralSelectorSP;

class Ordering;
typedef Lib::SmartPtr<Ordering> OrderingSP;
};

namespace Indexing
{
class Index;
class IndexManager;
class TermSharing;
};

namespace Saturation
{
class SaturationAlgorithm;
typedef Lib::SmartPtr<SaturationAlgorithm> SaturationAlgorithmSP;

class ClauseContainer;
class UnprocessedClauseContainer;

class PassiveClauseContainer;
typedef Lib::SmartPtr<PassiveClauseContainer> PassiveClauseContainerSP;

class ActiveClauseContainer;
}

namespace Inferences
{
class InferenceEngine;

class GeneratingInferenceEngine;
typedef Lib::SmartPtr<GeneratingInferenceEngine> GeneratingInferenceEngineSP;

class ForwardSimplificationEngine;
typedef Lib::SmartPtr<ForwardSimplificationEngine> ForwardSimplificationEngineSP;

class BackwardSimplificationEngine;
typedef Lib::SmartPtr<BackwardSimplificationEngine> BackwardSimplificationEngineSP;
}

#endif /* __Forwards__ */
