/**
 * @file TermSharing.hpp
 * Defines class TermSharing.
 *
 * @since 28/12/2007 Manchester
 */

#ifndef __TermSharing__
#define __TermSharing__

#include "../Lib/Set.hpp"
#include "../Kernel/Term.hpp"

using namespace Lib;
using namespace Kernel;

namespace Indexing {

class TermSharing
{
public:
  TermSharing();
  ~TermSharing();
  Term* insert(Term*);
  Literal* insert(Literal*);
  Term* insertRecurrently(Term*);
  /** The hash function of this term */
  inline static unsigned hash(const Literal* l)
  { return l->hash(); }
  /** The hash function of this term */
  inline static unsigned hash(const Term* t)
  { return t->hash(); }
  static bool equals(const Term* t1,const Term* t2);
  /** True if the two literals are equal */
  static bool equals(const Literal* l1,const Literal* l2)
  { return l1->polarity() == l2->polarity() &&
           equals(static_cast<const Term*>(l1),
		  static_cast<const Term*>(l2)); }
private:
  /** The set storing all terms */
  Set<Term*,TermSharing> _terms;
  /** The set storing all literals */
  Set<Literal*,TermSharing> _literals;
  /** Number of terms stored */
  unsigned _totalTerms;
  /** Number of ground terms stored */
  unsigned _groundTerms;
  /** Number of literals stored */
  unsigned _totalLiterals;
  /** Number of ground literals stored */
  unsigned _groundLiterals;
  /** Number of literal insertions */
  unsigned _literalInsertions;
  /** Number of term insertions */
  unsigned _termInsertions;
}; // class TermSharing

} // namespace Indexing

#endif
