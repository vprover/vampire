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
 * @file KBOComparator.hpp
 * Defines comparator class for KBO.
 */

#ifndef __KBOComparator__
#define __KBOComparator__

#include "Forwards.hpp"

#include "Lib/Stack.hpp"

#include "KBO.hpp"

namespace Kernel {


/**
 * Runtime specialized KBO ordering check, based on the linear KBO check
 * also implemented in @b KBO.
 */
class KBOComparator
: public OrderingComparator
{
public:
  /** The runtime specialization happens in the constructor. */
  KBOComparator(TermList tl1, TermList tl2, const KBO& kbo);

  /** Executes the runtime specialized instructions with concrete substitution. */
  bool check(const SubstApplicator* applicator) const;
  std::string toString() const override;

private:
  // TODO this could be done with KBO::State
  static void countSymbols(const KBO& kbo, Lib::DHMap<unsigned,int>& vars, int& w, TermList t, int coeff);

  enum InstructionTag {
    DATA = 0u,
    WEIGHT = 1u,
    COMPARE_VV = 2u,
    COMPARE_VT = 3u,
    COMPARE_TV = 4u,
    SUCCESS = 5u,
  };

  /**
   * Stores atomic instructions for KBO.
   * We have 64 bits per instruction, and the following combinations (where ?> denotes checking >):
   * - success
   * - weight check:          w + |var_i o \theta|_v * nvar_i ?> 0
   * - compare var with var:  (var1 o \theta) ?> (var2 o \theta)
   * - compare var with term: (var o \theta) ?> (term o \theta)
   * - compare term with var: (term o \theta) ?> (var o \theta)
   *
   * and the following layout of instructions:
   * |      first instruction         |      second instruction    | ...
   * | 3 bits     | 29 bits | 32 bits | 3 bits | 29 bits | 32 bits |
   * | SUCCESS    |
   * | WEIGHT     |  arity  |    w    | DATA   | var_i   | nvar_i  | ... (this block `arity` times)
   * | COMPARE_VV |  var1   |  var2   |
   * | COMPARE_VT |  var    | <empty> |           term             |
   * | COMPARE_TV |  var    | <empty> |           term             |
   */
  struct Instruction {
    static Instruction term(Term* t) {
      Instruction ins;
      ins._setTag(InstructionTag::DATA);
      ins._setTerm(t);
      return ins;
    }
    static Instruction uintUint(InstructionTag t, unsigned v1 = 0, unsigned v2 = 0) {
      Instruction ins;
      ins._content = 0; // to silence a gcc warning (we set all bits below anyway)
      ins._setTag(t);
      ins._setFirstUint(v1);
      ins._setSecondUint(v2);
      return ins;
    }

    static constexpr unsigned
      TAG_BITS_START = 0,
      TAG_BITS_END = TAG_BITS_START + 3,
      FIRST_UINT_BITS_START = TAG_BITS_END,
      FIRST_UINT_BITS_END = FIRST_UINT_BITS_START + 29,
      SECOND_UINT_BITS_START = FIRST_UINT_BITS_END,
      SECOND_UINT_BITS_END = SECOND_UINT_BITS_START + 32,
      COEFF_BITS_START = FIRST_UINT_BITS_END,
      COEFF_BITS_END = COEFF_BITS_START + 32,
      TERM_BITS_START = 0,
      TERM_BITS_END = CHAR_BIT * sizeof(Term *);

    static_assert(TAG_BITS_START == 0, "tag must be the least significant bits");
    static_assert(TERM_BITS_START == 0, "term must be the least significant bits");
    static_assert(sizeof(void *) <= sizeof(uint64_t), "must be able to fit a pointer into a 64-bit integer");
    static_assert(InstructionTag::SUCCESS < 8, "must be able to squash tags into 3 bits");

    BITFIELD64_GET_AND_SET(unsigned, tag, Tag, TAG)
    BITFIELD64_GET_AND_SET(unsigned, firstUint, FirstUint, FIRST_UINT)
    BITFIELD64_GET_AND_SET(unsigned, secondUint, SecondUint, SECOND_UINT)
    BITFIELD64_GET_AND_SET(int, coeff, Coeff, COEFF)
    BITFIELD64_GET_AND_SET_PTR(Term*, term, Term, TERM)

  private:
    uint64_t _content;
  };
  const KBO& _kbo;
  Lib::Stack<Instruction> _instructions;
};

}
#endif
