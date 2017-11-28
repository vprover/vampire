
/*
 * File compit2.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file compit2.hpp
 * Defines compit2 interface for indexes.
 *
 * compitXY methods in this file are to be defined by index implementer
 * and will be called by the COMPIT2 shell located in compit2.cpp.
 *
 */


#ifndef __compit2__
#define __compit2__

#include "Kernel/Term.hpp"

typedef int32_t WORD;
#define TERM_SEPARATOR 0x7FFFFFFF

/**
 * TermStruct should be set to be an alias of the type that
 * represents terms.
 */
typedef Kernel::TermList TermStruct;

/**
 * Initializes the index structure. The benchmark will use
 * @b symCnt symbols, first @b fnSymCnt can appear inside
 * a term, other can appear only at the top level.
 *
 * If we're dealing with a superposition benchmark, symCnt
 * will be equal to the fnSymCnt. For a resolution benchmark,
 * symbols X, @b symCnt>X>=@b fnSymCnt were predicate symbols
 * in the original problem.
 */
void compitInit(unsigned symCnt, unsigned fnSymCnt);

/**
 * Specifies arity of a signature symbol. First call
 * to this method is with @b functor equal to 0, in each
 * successive call, this value increases by one, last call
 * is with @b functor == @b symCnt-1.
 */
void compitAddSymbol(unsigned functor, unsigned arity);

/**
 * Is called when we start assembling a new term.
 */
void compitTermBegin();
/**
 * Is called, when the next symbol in the reverse polish
 * notation is @b var-th variable. A term representation
 * of this variable should be returned.
 */
TermStruct compitTermVar(unsigned var);
/**
 * Is called, when the next symbol in the reverse polish
 * notation is a function symbol. A term representation
 * of the function should be returned.
 */
TermStruct compitTermFn(unsigned functor);

/**
 * Insert @b t into the indexing structure.
 */
void compitInsert(TermStruct t);
/**
 * Delete @b t from the indexing structure.
 */
void compitDelete(TermStruct t);
/**
 * Return number of terms in the indexing structure that
 * are unifiable with @b t.
 */
unsigned compitQuery(TermStruct t);


#endif /* __compit2__ */
