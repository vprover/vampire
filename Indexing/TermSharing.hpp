
/*
 * File TermSharing.hpp.
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

  Term* insert(Term*);
  Term* insertRecurrently(Term*);

  Literal* insert(Literal*);
  Literal* insertVariableEquality(Literal* lit,unsigned sort);

  Literal* tryGetOpposite(Literal* l);

  /** The hash function of this literal */
  inline static unsigned hash(const Literal* l)
  { return l->hash(); }
  /** The hash function of this term */
  inline static unsigned hash(const Term* t)
  { return t->hash(); }
  static bool equals(const Term* t1,const Term* t2);

  static bool equals(const Literal* l1, const Literal* l2, bool opposite=false);

  struct OpLitWrapper {
    OpLitWrapper(Literal* l) : l(l) {}
    Literal* l;
  };
  inline static unsigned hash(const OpLitWrapper& w)
  { return w.l->oppositeHash(); }
  static bool equals(const Literal* l1,const OpLitWrapper& w) {
    return equals(l1, w.l, true);
  }

private:
  bool argNormGt(TermList t1, TermList t2);

  /** The set storing all terms */
  Set<Term*,TermSharing> _terms;
  /** The set storing all literals */
  Set<Literal*,TermSharing> _literals;
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
}; // class TermSharing

} // namespace Indexing

#endif
