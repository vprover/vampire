/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#ifndef __SMTLIBLogic__
#define __SMTLIBLogic__

namespace Shell {

/**
  * SMT-LIB logics
  * QF (quantifier free) should be ground
  * A - arrays
  * (L/N)(I/R/both)A - linear/non-linear integer/real/both arithmetic
  * BV - bit vector - we don't support
  * (I/R)DL - difference logic - we don't treat specially (fragment of L(I/R)A)
  * UF - uninterpreted function = first order we know and love
  * DT - datatypes (term algebras)
  *
  * https://en.wikipedia.org/wiki/X_macro
  */

#define SMTLIBLogic_X\
  X(ALIA)\
  X(ALL)\
  X(ANIA)\
  X(AUFDTLIA)\
  X(AUFDTLIRA)\
  X(AUFDTNIRA)\
  X(AUFLIA)\
  X(AUFLIRA)\
  X(AUFNIA)\
  X(AUFNIRA)\
  X(BV)\
  X(LIA)\
  X(LRA)\
  X(NIA)\
  X(NRA)\
  X(QF_ABV)\
  X(QF_ALIA)\
  X(QF_ANIA)\
  X(QF_AUFBV)\
  X(QF_AUFLIA)\
  X(QF_AUFNIA)\
  X(QF_AX)\
  X(QF_BV)\
  X(QF_IDL)\
  X(QF_LIA)\
  X(QF_LIRA)\
  X(QF_LRA)\
  X(QF_NIA)\
  X(QF_NIRA)\
  X(QF_NRA)\
  X(QF_RDL)\
  X(QF_UF)\
  X(QF_UFBV)\
  X(QF_UFIDL)\
  X(QF_UFLIA)\
  X(QF_UFLRA)\
  X(QF_UFNIA)\
  X(QF_UFNRA)\
  X(UF)\
  X(UFBV)\
  X(UFDT)\
  X(UFDTLIA)\
  X(UFDTLIRA)\
  X(UFDTNIA)\
  X(UFDTNIRA)\
  X(UFIDL)\
  X(UFLIA)\
  X(UFLRA)\
  X(UFNIA)\
  X(UNDEFINED)

#define X(N) N,
enum class SMTLIBLogic {
  SMTLIBLogic_X
};
#undef X

}

#endif // __SMTLIBLogic__
