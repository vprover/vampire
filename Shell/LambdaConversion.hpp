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
 * @file LambdaElimination.hpp
 * Defines class LambdaElimination.
 */

#ifndef __LambdaConversion__
#define __LambdaConversion__

#if VHOL

#include "Lib/Deque.hpp"
#include "Forwards.hpp"

using namespace Kernel;
using namespace Shell;

/**
 * A class that converts lamba terms from named to nameless (De Bruijn indices) representation.
 * 
 * Along the way, it also converts formulas to terms with proxy symbols for connectives
 */
class LambdaConversion {
public:

  typedef pair<int,TermList> IndexSortPair;
  typedef DHMap<unsigned, IndexSortPair> VarToIndexMap;

  LambdaConversion() {};
//  LambdaElimination(DHMap<unsigned,TermList> varSorts) : _varSorts(varSorts){};

  TermList convertLambda(Term* lambdaTerm);
  TermList convertLambda(TermList term);
  TermList convertLambda(Formula*);
  
  //void addFunctionExtensionalityAxioms(UnitList*& units);
  //void addBooleanExtensionalityAxiom(UnitList*& units);
  
  static void addProxyAxioms(Problem& prb);
  static void addFunctionExtensionalityAxiom(Problem& prb);
  static void addChoiceAxiom(Problem& prb);
  static Literal* toEquality(TermList booleanTerm, bool polarity);

private:
    
  TermList convertLambda(TermList term, VarToIndexMap& map);
  TermList convertLambda(VList* vars, SList* sorts, TermList body, TermList bodySort, VarToIndexMap& map);
  TermList convertLambda(Formula*, VarToIndexMap& map);
      
  TermList sortOf(TermList t);
};

#endif

#endif // __LambdaConversion__
