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

namespace Lib
{
struct EmptyStruct {};
typedef void (*VoidFunc)();

template<typename T> class VirtualIterator;
template<typename T, template<class> class ref_t> class ArrayishObjectIterator;

template<typename T> class ScopedPtr;
template<typename T> class SmartPtr;

template<typename T> class SingleParamEvent;

template<class C> class DArray;
template<class C> class Stack;
template<class C> class Vector;
template<typename T> class List;
template<typename T> class SharedSet;

typedef List<int> IntList;
typedef Stack<vstring> StringStack;
typedef List<VoidFunc> VoidFuncList;

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
using namespace Lib;

class Signature;

class Term;
class TermList;
typedef VirtualIterator<TermList> TermIterator;
typedef Stack<TermList> TermStack;

typedef List<unsigned> VList; // a list of variables (which are unsigned)
typedef List<TermList> SList; // a list of sorts (which are now, with polymorphism, TermLists)
typedef const SharedSet<unsigned> VarSet;

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
typedef VirtualIterator<Clause*> ClauseIterator;
typedef SingleParamEvent<Clause*> ClauseEvent;
typedef List<Clause*> ClauseList;
typedef Stack<Clause*> ClauseStack;

class Problem;

class Renaming;
class Substitution;

class RobSubstitutionTL;
typedef VirtualIterator<RobSubstitutionTL*> SubstIterator;
typedef Lib::SmartPtr<RobSubstitutionTL> RobSubstitutionSP;

class RobSubstitutionTS;
typedef VirtualIterator<RobSubstitutionTS*> SubstIteratorTS;
typedef Lib::SmartPtr<RobSubstitutionTS> RobSubstitutionTSSP;

class Matcher;
typedef VirtualIterator<Matcher*> MatchIterator;

class LiteralSelector;

class Ordering;
typedef Lib::SmartPtr<Ordering> OrderingSP;

typedef unsigned SplitLevel;
typedef const SharedSet<SplitLevel> SplitSet;

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
class LiteralIndex;
class LiteralIndexingStructure;
class TermIndex;
class TermIndexingStructure;

class TermSharing;

class ResultSubstitution;
typedef Lib::SmartPtr<ResultSubstitution> ResultSubstitutionSP;
//typedef Lib::VirtualIterator<ResultSubstitutionSP> SubstSPIterator;

enum class SplittingAlgo { NONE 
#if VHOL
  , HOL_MATCH
  , HOL_UNIF
#endif
                         };

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
using namespace Lib;

class SATClause;
class SATLiteral;
class SATInference;
class SATSolver;

typedef VirtualIterator<SATClause*> SATClauseIterator;
typedef List<SATClause*> SATClauseList;
typedef Stack<SATClause*> SATClauseStack;
typedef Stack<SATLiteral> SATLiteralStack;
}

namespace Shell
{
class Options;
class Property;
class Statistics;
}

#endif /* __Forwards__ */
