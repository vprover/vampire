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

using namespace Lib;
using namespace Kernel;

namespace Indexing {

class TermSharing
{
public:
  CLASS_NAME(TermSharing);
  USE_ALLOCATOR(TermSharing);

  TermSharing();
  ~TermSharing();

  // TODO we should probably inline the common path where a term already exists
  Term* insert(Term*);

  AtomicSort* insert(AtomicSort*);

  Literal* insert(Literal*);
  Literal* insertVariableEquality(Literal* lit,TermList sort);

  Literal* tryGetOpposite(Literal* l);

  void setPoly();

  /** The hash function of this literal */
  inline static unsigned hash(const Literal* l)
  { return l->hash(); }
  /** The hash function of this term */
  inline static unsigned hash(const Term* t)
  { return t->hash(); }
  static bool equals(const Term* t1,const Term* t2);

  template<bool opposite = false>
  static bool equals(const Literal* l1, const Literal* l2);

  DHSet<TermList>* getArraySorts(){
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
  int sumRedLengths(TermStack& args);
  bool argNormGt(TermList t1, TermList t2);

  /** The set storing all terms */
  Set<Term*,TermSharing> _terms;
  /** The set storing all literals */
  Set<Literal*,TermSharing> _literals;
  /** The set storing all sorts */
  Set<AtomicSort*,TermSharing> _sorts;
  /* Set containing all array sorts. 
   * Can be deleted once array axioms are made truly poltmorphic
   */  
  DHSet<TermList> _arraySorts;

  bool _poly;
  bool _wellSortednessCheckingDisabled;
}; // class TermSharing

} // namespace Indexing

#endif
