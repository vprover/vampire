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

#if VTHREADED
#include <mutex>
#define ACQ_TERM_SHARING_LOCK const std::lock_guard<std::recursive_mutex>\
  __vampire_term_sharing_lock(Indexing::TermSharing::_mutex)
#else
#define ACQ_TERM_SHARING_LOCK
#endif

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

#if VTHREADED
  /** The hash function of this term */
  inline static unsigned hash(std::pair<Signature*, Term*> item)
  { return item.second->hashUnderSignature(item.first); }

  /** The hash function of this literal */
  inline static unsigned hash(std::pair<Signature*, Literal*> item)
  { return item.second->hashUnderSignature(item.first); }

  inline static unsigned hash(std::pair<Signature*, OpLitWrapper> item)
  { return item.second.l->oppositeHashUnderSignature(item.first); }

  static bool equals(
    std::pair<Signature*, Term*> left,
    std::pair<Signature*, Term*> right
  );
  static bool equals(
    std::pair<Signature*, Literal*> left,
    std::pair<Signature*, Literal*> right,
    bool opposite=false
  );
  static bool equals(
    std::pair<Signature*, Literal*> left,
    std::pair<Signature*, OpLitWrapper> right
  ) {
    return equals(left, std::make_pair(right.first, right.second.l), true);
  }
#else
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
#endif

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
// instance-level mutex
#if VTHREADED
  static std::recursive_mutex _mutex;
  friend class Kernel::Signature;
#endif

  bool argNormGt(TermList t1, TermList t2);

#if VTHREADED
  /** The set storing all terms */
  Set<std::pair<Signature*, Term*>,TermSharing> _terms;
  /** The set storing all literals */
  Set<std::pair<Signature*, Literal*>,TermSharing> _literals;
#else
  /** The set storing all terms */
  Set<Term*,TermSharing> _terms;
  /** The set storing all literals */
  Set<Literal*,TermSharing> _literals;
#endif
  /** Number of terms stored */
  unsigned _totalTerms;
  /** Number of ground terms stored */
  // unsigned _groundTerms; // MS: unused
  /** Number of literals stored */
  unsigned _totalLiterals;
  /** Number of ground literals stored */
  // unsigned _groundLiterals; // MS: unused
  /** Number of literal insertions */
  unsigned _literalInsertions;
  /** Number of term insertions */
  unsigned _termInsertions;

  bool _poly;
  bool _wellSortednessCheckingDisabled;
}; // class TermSharing

} // namespace Indexing

#endif