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
 * @file TermSharing.hpp
 * Defines class TermSharing.
 *
 * @since 28/12/2007 Manchester
 */

#ifndef __TermSharing__
#define __TermSharing__

#include "Lib/Set.hpp"
#include "Kernel/Term.hpp"

#include "Lib/Allocator.hpp"

using namespace Kernel;

namespace Indexing {

class TermSharing
{
public:
  TermSharing();
  ~TermSharing();

  // TODO we should probably inline the common path where a term already exists
  // not quite sure what that todo exactly meant but I think it should be resolved now (?)
  void computeAndSetSharedTermData(Term*);
  void computeAndSetSharedSortData(AtomicSort*);
  void computeAndSetSharedLiteralData(Literal*);
  void computeAndSetSharedVarEqData(Literal*, TermList eqSort);

  Literal* tryGetOpposite(Literal* l);

  void setPoly();

  /** The hash function of this literal */
  inline static unsigned hash(const Literal* l)
  { return l->hash(); }
  /** The hash function of this term */
  inline static unsigned hash(const Term* t)
  { return t->hash(); }
  static bool equals(const Term* t1,const Term* t2);

  /**
   * True if the two literals are equal (or equal except polarity if @c opposite is true)
   */
  template<bool opposite = false>
  static bool equals(const Literal* l1, const Literal* l2)
  { return Literal::literalEquals(l1, l2->functor(), l2->polarity() ^ opposite, 
        [&](auto i){ return *l2->nthArgument(i); }, 
        l2->arity(), Lib::someIf(l2->isTwoVarEquality(), [&](){ return l2->twoVarEqSort(); }), l2->commutative()); }

  Lib::DHSet<TermList>* getArraySorts(){
    return &_arraySorts;
  }

  struct OpLitWrapper {
    OpLitWrapper(Literal* l) : l(l) {}
    Literal* l;
  };
  inline static unsigned hash(const OpLitWrapper& w)
  { return w.l->hash<true>(); }
  static bool equals(const Literal* l1,const OpLitWrapper& w) {
    return equals<true>(l1, w.l);
  }

  // stuff for disabling a well-sortedness check
  // still used, but only in BlockedClauseElimination: can we eliminate that occurrence?
  class WellSortednessCheckingLocalDisabler {
    TermSharing* _tsInstance;
    bool _valueToRestore;
  public:
    WellSortednessCheckingLocalDisabler(TermSharing* tsInstance) {
      _tsInstance = tsInstance;
      _valueToRestore = _tsInstance->_wellSortednessCheckingDisabled;
      _tsInstance->_wellSortednessCheckingDisabled = true;
    }
    ~WellSortednessCheckingLocalDisabler() {
      _tsInstance->_wellSortednessCheckingDisabled = _valueToRestore;
    }
  };
  bool isWellSortednessCheckingDisabled() const { return _wellSortednessCheckingDisabled; }

private:
  friend class Kernel::Term;
  friend class Kernel::Literal;
  friend class Kernel::AtomicSort;
  int sumRedLengths(TermStack& args);
  static bool argNormGt(TermList t1, TermList t2);

  /** The set storing all terms */
  Lib::Set<Term*,TermSharing> _terms;
  /** The set storing all literals */
  Lib::Set<Literal*,TermSharing> _literals;
  /** The set storing all sorts */
  Lib::Set<AtomicSort*,TermSharing> _sorts;
  /* Set containing all array sorts. 
   * Can be deleted once array axioms are made truly poltmorphic
   */  
  Lib::DHSet<TermList> _arraySorts;

  bool _poly;
  bool _wellSortednessCheckingDisabled;
}; // class TermSharing


} // namespace Indexing

#endif
