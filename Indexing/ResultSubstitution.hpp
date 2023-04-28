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
 * @file ResultSubstitution.hpp
 * Defines class ResultSubstitution.
 */


#ifndef __ResultSubstitution__
#define __ResultSubstitution__

#include "Forwards.hpp"

#include "Lib/SmartPtr.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Renaming.hpp"

namespace Indexing {

using namespace Kernel;

/**
 * Represents a substitution, that has been retrieved from an
 * indexing structure.
 *
 * It distinguishes two classes of terms/literals --
 * query and result ones. Variables in query
 * terms/literals have the same meaning as variables in query
 * that was the indexing structure asked, and variables in
 * result terms/literals have the meaning of variables in the
 * term/literal that was retrieved from the index.
 */
class ResultSubstitution
{
public:
  virtual ~ResultSubstitution() {}
  virtual TermList applyToQuery(TermList t) { NOT_IMPLEMENTED; }
  virtual Literal* applyToQuery(Literal* l) { NOT_IMPLEMENTED; }
  virtual TermList applyToResult(TermList t) { NOT_IMPLEMENTED; }
  virtual Literal* applyToResult(Literal* l) { NOT_IMPLEMENTED; }

  virtual TermList applyTo(TermList t, VarBank bank) { ASSERTION_VIOLATION; }
  virtual Literal* applyTo(Literal* l, VarBank bank) { NOT_IMPLEMENTED; }

  /** if implementation cannot easily give result for this, zero is returned */
  virtual size_t getQueryApplicationWeight(TermList t) { return 0; }
  /** if implementation cannot easily give result for this, zero is returned */
  virtual size_t getQueryApplicationWeight(Literal* l) { return 0; }
  /** if implementation cannot easily give result for this, zero is returned */
  virtual size_t getResultApplicationWeight(TermList t) { return 0; }
  /** if implementation cannot easily give result for this, zero is returned */
  virtual size_t getResultApplicationWeight(Literal* l) { return 0; }
  /** return stack of constraints */
  virtual Recycled<LiteralStack> getConstraints() { NOT_IMPLEMENTED; }

  template<typename T>
  T apply(T t, bool result)
  {
    CALL("ResultSubstitution::apply")
    if(result) {
      return applyToResult(t);
    } else {
      return applyToQuery(t);
    }
  }

  bool isRenamingOn(TermList t, bool result);

  /** if implementation cannot easily give result for this, zero is returned */
  template<typename T>
  size_t getApplicationWeight(T t, bool result)
  {
    if(result) {
      return getResultApplicationWeight(t);
    } else {
      return getQueryApplicationWeight(t);
    }
  }

  /**
   * Apply substitution to result term that fulfills the condition,
   * that all its variables are bound to some term of the query.
   *
   * Applying this substitution makes sense, when
   * @b isIdentityOnQueryWhenResultBound() method returns true,
   * as then there's no need to apply the substitution to any
   * query terms.
   */
  virtual TermList applyToBoundResult(TermList t)
  { return applyToResult(t); }

  /**
   * Apply substitution to result term that fulfills the condition,
   * that all its variables are bound to some term of the query.
   *
   * Applying this substitution makes sense, when
   * @b isIdentityOnQueryWhenResultBound() method returns true,
   * as then there is no need to apply the substitution to any
   * query terms.
   */
  virtual Literal* applyToBoundResult(Literal* lit)
  { return applyToResult(lit); }

  /**
   * Return true if, when the substitution is applied to a result
   * term through the @b applyToBoundResult function, the corresponding
   * substitution for query terms is identity.
   */
  virtual bool isIdentityOnQueryWhenResultBound() {return false;}


  /**
   * Apply substitution to query term that fulfills the condition,
   * that all its variables are bound to some term of the result.
   *
   * Applying this substitution makes sense, when
   * @b isIdentityOnResultWhenQueryBound() method returns true,
   * as then there is no need to apply the substitution to any
   * result terms.
   */
  virtual TermList applyToBoundQuery(TermList t)
  { return applyToQuery(t); }

  /**
   * Return true if, when the substitution is applied to a query
   * term through the @b applyToBoundQuery function, the corresponding
   * substitution for query terms is identity.
   */
  virtual bool isIdentityOnResultWhenQueryBound() {return false;}

  static ResultSubstitutionSP fromSubstitution(RobSubstitutionTL* s, VarBank queryBank, VarBank resultBank);
  virtual void output(std::ostream& ) const = 0;
  friend std::ostream& operator<<(std::ostream& out, ResultSubstitution const& self)
  { self.output(out); return out; }
};

}; // namepace Indexing

#endif /* __ResultSubstitution__ */
