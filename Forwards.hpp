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

#include <memory>

namespace Lib
{
struct EmptyStruct {};
typedef void (*VoidFunc)();

template<typename T> class VirtualIterator;

template<typename T> class ScopedPtr;
template<typename T> class SmartPtr;

template<typename T> class SingleParamEvent;

template<class C> class DArray;
template<class C> class Stack;
template<class C> class Vector;
template<typename T> class List;
template<typename T> class SharedSet;

typedef Lib::List<int> IntList;
typedef Lib::Stack<std::string> StringStack;
typedef Lib::List<VoidFunc> VoidFuncList;

class DefaultHash;
class DefaultHash2;
template <typename Key, typename Val,class Hash=DefaultHash> class Map;
template<class A, class B, class HashA=DefaultHash, class HashB=DefaultHash> class BiMap;
template <typename Key, typename Val, class Hash1=DefaultHash, class Hash2=DefaultHash2> class DHMap;
template <typename Val, class Hash1=DefaultHash, class Hash2=DefaultHash2> class DHSet;
template <typename Val, class Hash1=DefaultHash, class Hash2=DefaultHash2> class DHMultiset;
template <typename Val, class Hash=DefaultHash> class Set;

class Timer;
};

namespace Kernel
{

class Signature;

class Term;
class TermList;
typedef Lib::VirtualIterator<TermList> TermIterator;
typedef Lib::Stack<TermList> TermStack;

struct SubstApplicator;
struct AppliedTerm;

typedef Lib::List<unsigned> VList; // a list of variables (which are unsigned)
typedef Lib::List<TermList> SList; // a list of sorts (which are now, with polymorphism, TermLists)
typedef const Lib::SharedSet<unsigned> VarSet;


class Literal;
typedef Lib::List<Literal*> LiteralList;
typedef Lib::Stack<Literal*> LiteralStack;
typedef Lib::VirtualIterator<Literal*> LiteralIterator;

class Inference;

class Unit;
typedef Lib::List<Unit*> UnitList;
typedef Lib::Stack<Unit*> UnitStack;
typedef Lib::VirtualIterator<Unit*> UnitIterator;

class FormulaUnit;
class Formula;
typedef Lib::List<Formula*> FormulaList;
typedef Lib::VirtualIterator<Formula*> FormulaIterator;
typedef Lib::Stack<Formula*> FormulaStack;

class Clause;
typedef Lib::VirtualIterator<Clause*> ClauseIterator;
typedef Lib::SingleParamEvent<Clause*> ClauseEvent;
typedef Lib::List<Clause*> ClauseList;
typedef Lib::Stack<Clause*> ClauseStack;

class Problem;

class Renaming;
class Substitution;

class RobSubstitution;
typedef Lib::VirtualIterator<RobSubstitution*> SubstIterator;
typedef Lib::SmartPtr<RobSubstitution> RobSubstitutionSP;

class Matcher;
typedef Lib::VirtualIterator<Matcher*> MatchIterator;

class LiteralSelector;

class Ordering;
typedef Lib::SmartPtr<Ordering> OrderingSP;
struct OrderingComparator;
typedef std::unique_ptr<const OrderingComparator> OrderingComparatorUP;

typedef unsigned SplitLevel;
typedef const Lib::SharedSet<SplitLevel> SplitSet;

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

enum class SymbolType{FUNC, PRED, TYPE_CON};

};

namespace Indexing
{
class Index;
class IndexManager;
template<class Data>
class LiteralIndex;
template<class Data>
class TermIndex;
template<class Data>
class TermIndexingStructure;

class TermSharing;

class ResultSubstitution;
typedef Lib::SmartPtr<ResultSubstitution> ResultSubstitutionSP;
};

namespace Saturation
{
class SaturationAlgorithm;

class ClauseContainer;
class UnprocessedClauseContainer;
class PassiveClauseContainer;
class ActiveClauseContainer;
}

namespace Inferences
{
class InferenceEngine;
class GeneratingInferenceEngine;
class ImmediateSimplificationEngine;
class ForwardSimplificationEngine;
class BackwardSimplificationEngine;
}

namespace SAT
{

class SATClause;
class SATLiteral;
class SATInference;
class SATSolver;

typedef Lib::VirtualIterator<SATClause*> SATClauseIterator;
typedef Lib::List<SATClause*> SATClauseList;
typedef Lib::Stack<SATClause*> SATClauseStack;
typedef Lib::Stack<SATLiteral> SATLiteralStack;
}

namespace Shell
{
class Options;
class Property;
class Statistics;
class FunctionDefinitionHandler;
class ConditionalRedundancyHandler;
struct ConditionalRedundancyEntry;
}
#endif /* __Forwards__ */
