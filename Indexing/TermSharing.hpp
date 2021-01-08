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

#if VTHREADED
#include <mutex>
#endif

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

  Term* insert(Term*);
  Term* insertRecurrently(Term*);

  Literal* insert(Literal*);
  Literal* insertVariableEquality(Literal* lit,TermList sort);

  Literal* tryGetOpposite(Literal* l);

  void setPoly();
  struct OpLitWrapper {
    OpLitWrapper(Literal* l) : l(l) {}
    Literal* l;
  };

  /** The hash function of this term */
  inline static unsigned hash(const Term* t)
  { return t->hash(); }

  /** The hash function of this literal */
  inline static unsigned hash(const Literal* l)
  { return l->hash(); }

  inline static unsigned hash(const OpLitWrapper& w)
  { return w.l->oppositeHash(); }

  static bool equals(const Term* s,const Term* t);
  static bool equals(const Literal* l1, const Literal* l2, bool opposite=false);
  static bool equals(const Literal* l1,const OpLitWrapper& w) {
    return equals(l1, w.l, true);
  }

  friend class WellSortednessCheckingLocalDisabler;

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
#if VTHREADED
  // instance-level mutexes
  static std::mutex _term_mutex, _literal_mutex;
  friend class Kernel::Signature;
#endif

  bool argNormGt(TermList t1, TermList t2);

  /** The set storing all terms */
  Set<Term*,TermSharing> _terms;
  /** The set storing all literals */
  Set<Literal*,TermSharing> _literals;
  /** Number of terms stored */
  VATOMIC(unsigned) _totalTerms;
  /** Number of ground terms stored */
  // unsigned _groundTerms; // MS: unused
  /** Number of literals stored */
  VATOMIC(unsigned) _totalLiterals;
  /** Number of ground literals stored */
  // unsigned _groundLiterals; // MS: unused
  /** Number of literal insertions */
  VATOMIC(unsigned) _literalInsertions;
  /** Number of term insertions */
  VATOMIC(unsigned) _termInsertions;

  VATOMIC(bool) _poly;
  VATOMIC(bool) _wellSortednessCheckingDisabled;
}; // class TermSharing

} // namespace Indexing

#endif