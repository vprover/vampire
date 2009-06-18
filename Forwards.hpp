/**
 * @file Forwards.hpp
 * Forward declarations of some classes
 */

#ifndef __Forwards__
#define __Forwards__

#include "Config.hpp"

namespace Lib
{
template<typename T> class VirtualIterator;
template<typename T> class SmartPtr;
template<typename T> class SingleParamEvent;
template<class C> class DArray;
template<class C> class Stack;
template<typename T> class List;
template <typename T, class Comparator> class BinaryHeap;

template<typename T> class ArrayishObjectIterator;

template<typename T> class ArrayMap;

typedef List<int> IntList;


class BacktrackData;
};

namespace Kernel
{
using namespace Lib;

class Signature;

class TermList;
typedef VirtualIterator<TermList> TermIterator;
class Term;
class Literal;
typedef List<Literal*> LiteralList;

class Inference;

class Unit;
class FormulaUnit;
class Formula;
typedef List<Unit*> UnitList;

class Clause;
typedef VirtualIterator<Clause*> ClauseIterator;
typedef SingleParamEvent<Clause*> ClauseEvent;
typedef List<Clause*> ClauseList;

class DoubleSubstitution;
class Renaming;
class Substitution;

class RobSubstitution;
typedef VirtualIterator<RobSubstitution*> SubstIterator;
typedef Lib::SmartPtr<RobSubstitution> RobSubstitutionSP;

class EGSubstitution;
typedef VirtualIterator<EGSubstitution*> RSubstIterator;
typedef Lib::SmartPtr<EGSubstitution> EGSubstitutionSP;

class Matcher;
typedef VirtualIterator<Matcher*> MatchIterator;

class LiteralSelector;
typedef Lib::SmartPtr<LiteralSelector> LiteralSelectorSP;

class Ordering;
typedef Lib::SmartPtr<Ordering> OrderingSP;

class BDD;
class BDDNode;

};

namespace Indexing
{
class Index;
class IndexManager;
class LiteralIndex;
class LiteralIndexingStructure;
class TermIndex;
class TermIndexingStructure;
class TermSharing;

class ResultSubstitution;
typedef Lib::SmartPtr<ResultSubstitution> ResultSubstitutionSP;

class GeneratingLiteralIndex;
class SimplifyingLiteralIndex;
class UnitClauseSimplifyingLiteralIndex;
class FwSubsSimplifyingLiteralIndex;

class SubstitutionTree;
class LiteralSubstitutionTree;
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

class ImmediateSimplificationEngine;
typedef Lib::SmartPtr<ImmediateSimplificationEngine> ImmediateSimplificationEngineSP;

class ForwardSimplificationEngine;
typedef Lib::SmartPtr<ForwardSimplificationEngine> ForwardSimplificationEngineSP;

class BackwardSimplificationEngine;
typedef Lib::SmartPtr<BackwardSimplificationEngine> BackwardSimplificationEngineSP;
}

namespace Shell
{
class TPTPLexer;
class TPTPParser;
}


/**
 * Deletion of incomplete class types causes memory leaks. Using this
 * causes compile error when deleting incomplete classes.
 *
 * (see http://www.boost.org/doc/libs/1_36_0/libs/utility/checked_delete.html )
 */
template<class T> inline void checked_delete(T * x)
{
    // intentionally complex - simplification causes regressions
    typedef char type_must_be_complete[ sizeof(T)? 1: -1 ];
    (void) sizeof(type_must_be_complete);
    delete x;
}


#endif /* __Forwards__ */
