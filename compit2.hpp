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

typedef TermList TermStruct;

/**
 * Initializes the index structure. The benchmark will use
 * @b symCnt symbols, first @b fnSymCnt can appear inside
 * a term, other can appear only at the top level.
 */
void compitInit(unsigned symCnt, unsigned fnSymCnt);

/**
 * Specifies arity of a symbol from signature. First call
 * to this method is with @b functor equal to 0, in each
 * successive call, this value increases by one.
 */
void compitAddSymbol(unsigned functor, unsigned arity);

void compitTermBegin();
TermStruct compitTermVar(unsigned var);
TermStruct compitTermFn(unsigned functor);

void compitInsert(TermStruct t);
void compitDelete(TermStruct t);
unsigned compitQuery(TermStruct t);



#endif /* __compit2__ */
