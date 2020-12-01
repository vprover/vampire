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
  */
enum SMTLIBLogic {
  SMT_ALIA,
  SMT_ALL,
  SMT_AUFDTLIA,
  SMT_AUFDTLIRA,
  SMT_AUFDTNIRA,
  SMT_AUFNIA,
  SMT_AUFLIA,
  SMT_AUFLIRA,
  SMT_AUFNIRA,
  SMT_BV,
  SMT_LIA,
  SMT_LRA,
  SMT_NIA,
  SMT_NRA,
  SMT_QF_ABV,
  SMT_QF_ALIA,
  SMT_QF_ANIA,
  SMT_QF_AUFBV,
  SMT_QF_AUFLIA,
  SMT_QF_AUFNIA,
  SMT_QF_AX,
  SMT_QF_BV,
  SMT_QF_IDL,
  SMT_QF_LIA,
  SMT_QF_LIRA,
  SMT_QF_LRA,
  SMT_QF_NIA,
  SMT_QF_NIRA,
  SMT_QF_NRA,
  SMT_QF_RDL,
  SMT_QF_UF,
  SMT_QF_UFBV,
  SMT_QF_UFIDL,
  SMT_QF_UFLIA,
  SMT_QF_UFLRA,
  SMT_QF_UFNIA,
  SMT_QF_UFNRA,
  SMT_UF,
  SMT_UFBV,
  SMT_UFDT,
  SMT_UFDTLIA,
  SMT_UFDTLIRA,
  SMT_UFDTNIA,
  SMT_UFDTNIRA,
  SMT_UFIDL,
  SMT_UFLIA,
  SMT_UFLRA,
  SMT_UFNIA,
  SMT_UNDEFINED
};

}

#endif // __SMTLIBLogic__
