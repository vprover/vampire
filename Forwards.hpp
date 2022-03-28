/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file Forwards.hpp
 * Forward declarations of some classes
 */

#ifndef __Forwards__
#define __Forwards__

#include "Lib/VString.hpp"

typedef void (*VoidFunc)();

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
  
struct EmptyStruct {};

class Hash;
struct IdentityHash;
struct PtrIdentityHash;


template<typename T> class VirtualIterator;

typedef VirtualIterator<int> IntIterator;
typedef VirtualIterator<unsigned> UnsignedIterator;

template<typename T> class ScopedPtr;
template<typename T> class SmartPtr;

template<class T> class RCPtr;

template<typename T> class SingleParamEvent;
template<class C> class DArray;
template<class C> class Stack;
template<class C> class Vector;
template<typename T> class List;
template<typename T, class Comparator> class BinaryHeap;
template<typename T> class SharedSet;

template <typename Key, typename Val,class Hash=Lib::Hash> class Map;
template<class A, class B, class HashA = Lib::Hash, class HashB = Lib::Hash> class BiMap; 

template<typename T, template<class> class ref_t> class ArrayishObjectIterator;
template<typename T> class ArrayMap;
template<typename C> class Vector;

class ArraySet;

typedef List<int> IntList;
typedef List<VoidFunc> VoidFuncList;

typedef Stack<vstring> StringStack;

typedef Map<vstring,unsigned,Hash> SymbolMap;

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
struct RationalConstantType;
class RealConstantType;

/** Index of a variable */
typedef unsigned Var;

struct BoundId
{
  Var var;
  bool left;

  /** Create uninitialized BoundId */
  BoundId() {}
  BoundId(Var var, bool left) : var(var), left(left) {}

  BoundId operator-() const { return BoundId(var, !left); }
};

class CoeffNumber;
class BoundNumber;

class Constraint;
class Assignment;

class V2CIndex;

class Sorts;
class Signature;

typedef VirtualIterator<Var> VarIterator;
typedef RCPtr<Constraint> ConstraintRCPtr;
typedef List<Constraint*> ConstraintList;
typedef List<ConstraintRCPtr> ConstraintRCList;
typedef VirtualIterator<Constraint*> ConstraintIterator;
typedef Stack<Constraint*> ConstraintStack;
typedef Stack<ConstraintRCPtr> ConstraintRCStack;

class TermList;
typedef VirtualIterator<TermList> TermIterator;
typedef Stack<TermList> TermStack;

typedef List<unsigned> VList; // a list of variables (which are unsigned)
typedef List<TermList> SList; // a list of sorts (which are now, with polymorphism, TermLists)

typedef std::pair<std::pair<TermList,unsigned>,std::pair<TermList,unsigned>> UnificationConstraint;
typedef Stack<UnificationConstraint> UnificationConstraintStack;
typedef Lib::SmartPtr<UnificationConstraintStack> UnificationConstraintStackSP;

class Term;
typedef BiMap<unsigned, Term*> FuncSubtermMap;
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
typedef List<Formula*> FormulaList;
typedef VirtualIterator<Formula*> FormulaIterator;
typedef Stack<Formula*> FormulaStack;

class Clause;
/** Defined as VirtualIterator<Clause*> */
typedef VirtualIterator<Clause*> ClauseIterator;
typedef SingleParamEvent<Clause*> ClauseEvent;
typedef List<Clause*> ClauseList;
typedef Stack<Clause*> ClauseStack;

typedef VirtualIterator<Literal*> LiteralIterator;


class Problem;

class FlatTerm;
class Renaming;
class Substitution;

class RobSubstitution;
typedef VirtualIterator<RobSubstitution*> SubstIterator;
typedef Lib::SmartPtr<RobSubstitution> RobSubstitutionSP;

class Matcher;
typedef VirtualIterator<Matcher*> MatchIterator;

class TermTransformer;
class TermTransformerTransformTransformed;
class FormulaTransformer;
class FormulaUnitTransformer;

class LiteralSelector;
typedef Lib::SmartPtr<LiteralSelector> LiteralSelectorSP;

class Ordering;
typedef Lib::SmartPtr<Ordering> OrderingSP;

class Grounder;
class GlobalSubsumptionGrounder;
class IGGrounder;
typedef Lib::ScopedPtr<Grounder> GrounderSCP;

class BDD;
class BDDNode;

typedef unsigned SplitLevel;
typedef const SharedSet<SplitLevel> SplitSet;

typedef const SharedSet<unsigned> VarSet;

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

class TermSharing;

class ResultSubstitution;
typedef Lib::SmartPtr<ResultSubstitution> ResultSubstitutionSP;

struct SLQueryResult;
struct TermQueryResult;

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

class Splitter;
class ConsequenceFinder;
class LabelFinder;
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
class SATInference;

class SATSolver;
typedef ScopedPtr<SATSolver> SATSolverSCP;

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

namespace DP
{
class DecisionProcedure;
class ScopedDecisionProcedure;
}

/**
 * Deletion of incomplete class types causes memory leaks. Using this
 * causes compile error when deleting incomplete classes.
 *
 * (see http://www.boost.org/doc/libs/1_36_0/libs/utility/checked_delete.html )
 */
template<class T> inline void checked_delete(T * x)
{
    CALL("Forwards/checked_delete");
    // intentionally complex - simplification causes regressions
    typedef char type_must_be_complete[ sizeof(T)? 1: -1 ];
    (void) sizeof(type_must_be_complete);
    delete x;
}

namespace Solving
{
using namespace Lib;

/**
 * Represents number of decision points at a given moment.
 * Negative values have special meaning depending on where they occur.
 */
typedef int DecisionLevel;

class AssignmentSelector;
class VariableSelector;
class Solver;
class BoundsArray;
class BoundInfo;

typedef Stack<BoundInfo> BoundStack;
}


#endif /* __Forwards__ */
