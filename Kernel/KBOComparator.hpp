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

using namespace Lib;

class KBOComparator
: public OrderingComparator
{
public:
  KBOComparator(const KBO& kbo) : _kbo(kbo) {}
  static KBOComparator* create(TermList tl1, TermList tl2, const KBO& kbo);

  bool check(const SubstApplicator* applicator) const;
  friend std::ostream& operator<<(std::ostream& out, const KBOComparator& comparator);

private:
  // TODO this could be done with KBO::State
  static void countSymbols(const KBO& kbo, DHMap<unsigned,int>& vars, int& w, TermList t, int coeff);

  enum class InstructionTag : unsigned {
    WEIGHT,
    COMPARE_VV,
    COMPARE_VT,
    COMPARE_TV,
    SUCCESS,
  };
  union Instruction {
    explicit Instruction(unsigned v1, unsigned v2) { _v1 = v1; _v2._uint = v2; }
    explicit Instruction(unsigned v) { _v1 = v; }
    explicit Instruction(Term* t) { _t = t; }
    explicit Instruction(unsigned v1, int v2) { _v1 = v1; _v2._int = v2; }

    struct {
      unsigned _v1;
      union {
        int _int;
        unsigned _uint;
      } _v2;
    };
    Term* _t;

    static_assert(sizeof(Term*)==2*sizeof(unsigned));
    static_assert(sizeof(Term*)==2*sizeof(int));
  };
  const KBO& _kbo;
  Stack<Instruction> _instructions;
};

}
#endif
