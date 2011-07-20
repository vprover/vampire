/**
 * @file Forwards.hpp
 * Forward declarations of some classes
 */

#ifndef __Forwards__
#define __Forwards__

#include <string>

#include "Debug/Log.hpp"

#include "Config.hpp"

typedef void (*VoidFunc)();

namespace Lib
{

struct EmptyStruct {};


class Hash;
struct IdentityHash;
struct PtrIdentityHash;


template<typename T> class VirtualIterator;
template<typename T> class ScopedPtr;
template<typename T> class SmartPtr;
template<typename T> class SingleParamEvent;
template<class C> class DArray;
template<class C> class Stack;
template<typename T> class List;
template<typename T, class Comparator> class BinaryHeap;
template<typename T> class SharedSet;

template <typename Key, typename Val,class Hash=Lib::Hash> class Map;


template<typename T> class ArrayishObjectIterator;

template<typename T> class ArrayMap;
template<typename C> class Vector;

typedef ArrayMap<EmptyStruct> ArraySet;

typedef List<int> IntList;
typedef List<VoidFunc> VoidFuncList;

typedef Map<std::string,unsigned,Hash> SymbolMap;


template<typename T> struct FirstHashTypeInfo;
/**
 * First hash for DHMap and DHMultiset classes.
 */
#define FIRST_HASH(Cl) typename FirstHashTypeInfo<Cl>::Type

//There is a bug (what else can it be?) in the VS2008 compiler that
//requires the name of the template parameter in the declaration to
//be the same as the name of the parameter used in definition, as
//long as the parameter is used in another parameter's default value.
//
//E.g. if the first parameter name here would be K instead of Key, we
//would get a compiler error, because in the Lib/DHMap.hpp file the
//definition of the class starts with
//template <typename Key, typename Val, class Hash1, class Hash2> class DHMap
//                   ^^^
template <typename Key, typename Val, class Hash1=FIRST_HASH(Key), class Hash2=Hash> class DHMap;
template <typename Val, class Hash1=FIRST_HASH(Val), class Hash2=Hash> class DHSet;
template <typename K,typename V, class Hash1=FIRST_HASH(K), class Hash2=Hash> class MapToLIFO;

template <typename Val,class Hash=Lib::Hash> class Set;


template <typename Value,class ValueComparator> class SkipList;

template<class Arr> class ArrayishObjectIterator;
template<typename T> class PointerIterator;

class BacktrackData;

class Timer;

namespace Sys
{
class Semaphore;
class SyncPipe;
}
};

namespace Kernel
{
using namespace Lib;

class IntegerConstantType;
class RationalConstantType;
class RealConstantType;

class Sorts;
class Signature;

class BaseType;
class FunctionType;
class PredicateType;

class TermList;
typedef VirtualIterator<TermList> TermIterator;
typedef Stack<TermList> TermStack;
class Term;
class Literal;
typedef List<Literal*> LiteralList;
typedef Stack<Literal*> LiteralStack;
typedef VirtualIterator<Literal*> LiteralIterator;

class Inference;

class Unit;
typedef List<Unit*> UnitList;
typedef Stack<Unit*> UnitStack;
typedef VirtualIterator<Unit*> UnitIterator;

class FormulaUnit;
class Formula;
typedef VirtualIterator<Formula*> FormulaIterator;
typedef Stack<Formula*> FormulaStack;

class Clause;
/** Defined as VirtualIterator<Clause*> */
typedef VirtualIterator<Clause*> ClauseIterator;
typedef SingleParamEvent<Clause*> ClauseEvent;
typedef List<Clause*> ClauseList;
typedef Stack<Clause*> ClauseStack;

class FlatTerm;
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

class TermTransformer;
class FormulaTransformer;
class FormulaUnitTransformer;


class LiteralSelector;
typedef Lib::SmartPtr<LiteralSelector> LiteralSelectorSP;

class Ordering;
typedef Lib::SmartPtr<Ordering> OrderingSP;

class Grounder;
typedef Lib::ScopedPtr<Grounder> GrounderSCP;

class BDD;
class BDDNode;

typedef unsigned SplitLevel;
typedef SharedSet<SplitLevel> SplitSet;


/**
 * Color of a term
 *
 * To be used for symbol elimination or interpolant extraction.
 */
enum Color {
  COLOR_TRANSPARENT = 0u,
  COLOR_LEFT = 1u,
  COLOR_RIGHT = 2u,

  /**
   * This color can never occur
   *
   * It can be used as an initial value to mark that the color is
   * yet to be determined. */
  COLOR_INVALID = 3u
};

class MainLoop;
typedef Lib::SmartPtr<MainLoop> MainLoopSP;


namespace Algebra
{
class ArithmeticKB;
};

};

namespace Indexing
{
class Index;
class IndexManager;
class LiteralIndex;
class LiteralIndexingStructure;
class TermIndex;
class TermIndexingStructure;
class ClauseSubsumptionIndex;
class FormulaIndex;

class TermSharing;

class ResultSubstitution;
typedef Lib::SmartPtr<ResultSubstitution> ResultSubstitutionSP;

class SLQueryResult;
class TermQueryResult;

class GeneratingLiteralIndex;
class SimplifyingLiteralIndex;
class UnitClauseLiteralIndex;
class FwSubsSimplifyingLiteralIndex;

class SubstitutionTree;
class LiteralSubstitutionTree;

class CodeTree;
class TermCodeTree;
class ClauseCodeTree;

class CodeTreeTIS;
class CodeTreeLIS;
class CodeTreeSubsumptionIndex;

class ArithmeticIndex;
class ConstraintDatabase;
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

class Limits;
class Splitter;
class ConsequenceFinder;
class SymElOutput;
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

class BDDMarkingSubsumption;
}

namespace SAT
{
using namespace Lib;

class SATClause;
class SATLiteral;

class SATSolver;
typedef ScopedPtr<SATSolver> SATSolverSCP;
class TWLSolver;

class RestartStrategy;
typedef ScopedPtr<RestartStrategy> RestartStrategySCP;
class VariableSelector;
typedef ScopedPtr<VariableSelector> VariableSelectorSCP;
class RLCSelector;
class ClauseDisposer;
typedef ScopedPtr<ClauseDisposer> ClauseDisposerSCP;

typedef VirtualIterator<SATClause*> SATClauseIterator;
typedef List<SATClause*> SATClauseList;
typedef Stack<SATClause*> SATClauseStack;

typedef VirtualIterator<SATLiteral> SATLiteralIterator;
typedef Stack<SATLiteral> SATLiteralStack;

}

namespace Shell
{
class AnswerLiteralManager;
class LaTeX;
class Options;
class Property;
class Statistics;
class TPTPLexer;
class TPTPParser;

class EPRRestoring;
class EPRInlining;

namespace LTB
{
class Storage;
class Builder;
class Selector;
}
}

namespace InstGen
{
class IGAlgorithm;
class ModelPrinter;
}

namespace Tabulation
{
class TabulationAlgorithm;
class Producer;
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


namespace Lib
{

template<typename C>
struct Relocator
{
  static void relocate(C* oldAddr, void* newAddr)
  {
    new(newAddr) C( *oldAddr );
    oldAddr->~C();
  }
};


}

#endif /* __Forwards__ */
